import ir.IRException;
import ir.IRFunction;
import ir.IRInstruction;
import ir.IRPrinter;
import ir.IRProgram;
import ir.IRReader;
import ir.operand.IROperand;
import ir.operand.IRVariableOperand;

import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Optimizer A - Dead code elimination without reaching definitions and branch removal
 * Mark-sweep style
 * Mark all critical instruction and push to WorkList. 
 * For each used variable, mark all instructions that write to it. 
 * Delete any instruction that is not marked & deletable 
 */
public class OptimizerMain {

    public static void main(String[] args) throws Exception {
        if (args.length != 2) {
            System.err.println("Usage: java OptimizerMain <input.ir> <output.ir>");
            System.exit(1);
        }

        String input = args[0];
        String output = args[1];

        IRReader reader = new IRReader();
        IRProgram program;
        try {
            program = reader.parseIRFile(input);
        } catch (IRException e) {
            System.err.println("IR parse error: " + e.getMessage());
            throw e;
        }

        // Optimize each function
        for (IRFunction f : program.functions) {
            simpleDCE(f);
        }

        // Write optimized IR
        try (PrintStream ps = new PrintStream(new FileOutputStream(output))) {
            IRPrinter printer = new IRPrinter(ps);
            printer.printProgram(program);
        }
    }

    private static void simpleDCE(IRFunction f) {
        List<IRInstruction> insts = f.instructions;
        int n = insts.size();

        boolean[] marked = new boolean[n];
        ArrayDeque<Integer> worklist = new ArrayDeque<>();

        // Initialize
        for (int i = 0; i < n; i++) {
            IRInstruction inst = insts.get(i);
            if (isCritical(inst)) {
                marked[i] = true;
                worklist.addLast(i);
            }
        }

        // Mark - Propagate backwards through naive "writes-to" edges without reaching defs
        while (!worklist.isEmpty()) {
            int i = worklist.removeFirst();
            IRInstruction inst = insts.get(i);

            // collect used variables in this instruction
            Set<String> usedVars = getUsedVariableNames(inst);

            // for each used variable v, mark every instruction that writes v
            for (String v : usedVars) {
                for (int j = 0; j < n; j++) {
                    if (!marked[j] && writesToVariable(insts.get(j), v)) {
                        marked[j] = true;
                        worklist.addLast(j);
                    }
                }
            }
        }

        // Sweep - delete unmarked deletable instructions
        List<IRInstruction> newInsts = new ArrayList<>();
        for (int i = 0; i < n; i++) {
            IRInstruction inst = insts.get(i);

            if (!marked[i] && isDeletableIfUnmarked(inst)) {
                // delete it
                continue;
            }
            newInsts.add(inst);
        }

        f.instructions = newInsts;
    }

    // -------- Critical definition --------
    private static boolean isCritical(IRInstruction inst) {
        IRInstruction.OpCode op = inst.opCode;

        // Control flow / structural
        if (op == IRInstruction.OpCode.LABEL) return true;
        if (op == IRInstruction.OpCode.GOTO) return true;
        if (op == IRInstruction.OpCode.BREQ) return true;
        if (op == IRInstruction.OpCode.BRNEQ) return true;
        if (op == IRInstruction.OpCode.BRLT) return true;
        if (op == IRInstruction.OpCode.BRGT) return true;
        if (op == IRInstruction.OpCode.BRGEQ) return true;

        // Return
        if (op == IRInstruction.OpCode.RETURN) return true;

        // Calls
        if (op == IRInstruction.OpCode.CALL) return true;
        if (op == IRInstruction.OpCode.CALLR) return true;

        // Store
        if (op == IRInstruction.OpCode.ARRAY_STORE) return true;

        // ASSIGN has two forms in this codebase:
        //  - scalar: assign, dst, src (2 operands)
        //  - array write: assign, A, idx, val (3 operands)  -> side effect, must keep
        if (op == IRInstruction.OpCode.ASSIGN) {
            if (inst.operands != null && inst.operands.length == 3) {
                return true; // array element write
            }
        }

        // Everything else is non-critical by default
        return false;
    }

    // -------- Used variables -------
    private static Set<String> getUsedVariableNames(IRInstruction inst) {
        Set<String> used = new HashSet<>();
        IRInstruction.OpCode op = inst.opCode;
        IROperand[] ops = inst.operands;

        if (ops == null) return used;

        switch (op) {
            case ASSIGN: {
                if (ops.length == 2) {
                    // assign dst, src  => uses src
                    if (ops[1] instanceof IRVariableOperand) {
                        used.add(((IRVariableOperand) ops[1]).getName());
                    }
                } else if (ops.length == 3) {
                    // assign A, idx, val
                    // uses idx, val (A is an array variable but has no instruction-writers)
                    if (ops[1] instanceof IRVariableOperand) {
                        used.add(((IRVariableOperand) ops[1]).getName());
                    }
                    if (ops[2] instanceof IRVariableOperand) {
                        used.add(((IRVariableOperand) ops[2]).getName());
                    }
                }
                break;
            }
            case ADD:
            case SUB:
            case MULT:
            case DIV:
            case AND:
            case OR: {
                // op dst, a, b => uses a,b
                if (ops.length >= 3) {
                    if (ops[1] instanceof IRVariableOperand) used.add(((IRVariableOperand) ops[1]).getName());
                    if (ops[2] instanceof IRVariableOperand) used.add(((IRVariableOperand) ops[2]).getName());
                }
                break;
            }
            case BREQ:
            case BRNEQ:
            case BRLT:
            case BRGT:
            case BRGEQ: {
                // brXX label, x, y => uses x,y (label ignored)
                if (ops.length >= 3) {
                    if (ops[1] instanceof IRVariableOperand) used.add(((IRVariableOperand) ops[1]).getName());
                    if (ops[2] instanceof IRVariableOperand) used.add(((IRVariableOperand) ops[2]).getName());
                }
                break;
            }
            case RETURN: {
                // return v => uses v
                if (ops.length >= 1 && ops[0] instanceof IRVariableOperand) {
                    used.add(((IRVariableOperand) ops[0]).getName());
                }
                break;
            }
            case CALL: {
                // call func, arg1, arg2, ... => uses args
                for (int i = 1; i < ops.length; i++) {
                    if (ops[i] instanceof IRVariableOperand) used.add(((IRVariableOperand) ops[i]).getName());
                }
                break;
            }
            case CALLR: {
                // callr ret, func, arg1, arg2, ... => uses args (ret is def)
                for (int i = 2; i < ops.length; i++) {
                    if (ops[i] instanceof IRVariableOperand) used.add(((IRVariableOperand) ops[i]).getName());
                }
                break;
            }
            case ARRAY_STORE: {
                // array_store val, A, idx => uses val, idx (A ignored)
                if (ops.length >= 3) {
                    if (ops[0] instanceof IRVariableOperand) used.add(((IRVariableOperand) ops[0]).getName());
                    if (ops[2] instanceof IRVariableOperand) used.add(((IRVariableOperand) ops[2]).getName());
                }
                break;
            }
            case ARRAY_LOAD: {
                // array_load dst, A, idx => uses idx (A ignored), dst is def
                if (ops.length >= 3) {
                    if (ops[2] instanceof IRVariableOperand) used.add(((IRVariableOperand) ops[2]).getName());
                }
                break;
            }
            default:
                // LABEL/GOTO etc: no uses we care about
                break;
        }

        return used;
    }

    // -------- "writes-to" predicate --------
    private static boolean writesToVariable(IRInstruction inst, String varName) {
        IRInstruction.OpCode op = inst.opCode;
        IROperand[] ops = inst.operands;
        if (ops == null || ops.length == 0) return false;

        switch (op) {
            case ASSIGN: {
                // scalar assign: assign dst, src writes dst
                if (ops.length == 2 && ops[0] instanceof IRVariableOperand) {
                    return ((IRVariableOperand) ops[0]).getName().equals(varName);
                }
                // array assign (3 operands) is memory write
                return false;
            }
            case ADD:
            case SUB:
            case MULT:
            case DIV:
            case AND:
            case OR:
            case ARRAY_LOAD: {
                // op dst, ... writes dst
                if (ops[0] instanceof IRVariableOperand) {
                    return ((IRVariableOperand) ops[0]).getName().equals(varName);
                }
                return false;
            }
            case CALLR: {
                // callr ret, func, ... writes ret
                if (ops[0] instanceof IRVariableOperand) {
                    return ((IRVariableOperand) ops[0]).getName().equals(varName);
                }
                return false;
            }
            default:
                return false;
        }
    }

    // -------- What we are allowed to delete if not marked --------
    private static boolean isDeletableIfUnmarked(IRInstruction inst) {
        IRInstruction.OpCode op = inst.opCode;

        // Control flow / Side-effect ops
        if (op == IRInstruction.OpCode.LABEL) return false;
        if (op == IRInstruction.OpCode.GOTO) return false;
        if (op == IRInstruction.OpCode.BREQ) return false;
        if (op == IRInstruction.OpCode.BRNEQ) return false;
        if (op == IRInstruction.OpCode.BRLT) return false;
        if (op == IRInstruction.OpCode.BRGT) return false;
        if (op == IRInstruction.OpCode.BRGEQ) return false;
        if (op == IRInstruction.OpCode.RETURN) return false;
        if (op == IRInstruction.OpCode.CALL) return false;
        if (op == IRInstruction.OpCode.CALLR) return false;
        if (op == IRInstruction.OpCode.ARRAY_STORE) return false;

        // Scalar form
        if (op == IRInstruction.OpCode.ASSIGN) {
            return inst.operands != null && inst.operands.length == 2;
        }

        // Pure computations/load can be delete
        if (op == IRInstruction.OpCode.ADD) return true;
        if (op == IRInstruction.OpCode.SUB) return true;
        if (op == IRInstruction.OpCode.MULT) return true;
        if (op == IRInstruction.OpCode.DIV) return true;
        if (op == IRInstruction.OpCode.AND) return true;
        if (op == IRInstruction.OpCode.OR) return true;
        if (op == IRInstruction.OpCode.ARRAY_LOAD) return true;

        return false;
    }
}