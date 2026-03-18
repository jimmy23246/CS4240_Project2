import ir.*;
import ir.datatype.*;
import ir.operand.*;

import java.io.*;
import java.util.*;

// runs dce + copy prop + const folding on each function
public class OptimizerMain {

    public static void main(String[] args) throws Exception {
        if (args.length != 2) {
            System.err.println("ERROR - must havw <input.ir> <output.ir>");
            System.exit(1);
        }

        IRReader reader = new IRReader();
        IRProgram program;
        try {
            program = reader.parseIRFile(args[0]);
        } catch (IRException e) {
            System.err.println("IR parse error - " + e.getMessage());
            throw e;
        }

        for (IRFunction f : program.functions) {
            optimizer(f);
        }

        try (PrintStream ps = new PrintStream(new FileOutputStream(args[1]))) {
            IRPrinter printer = new IRPrinter(ps);
            printer.printProgram(program);
        }
    }

    // Inner classes

    private static class BasicBlock {
        int id, start, end;
        List<Integer> preds = new ArrayList<>();
        List<Integer> succs = new ArrayList<>();
        BitSet gen, kill, in, out;
    }

    private static class ReachingDefsResult {
        int numDefs;
        int[] defInst;          // defIndex -> instruction index
        int[] instDefIdx;       // instruction index -> defIndex (-1 if not a def)
        Map<String, List<Integer>> varDefs; // varName -> list of defIndices
        BitSet[] reachingDefs;
        List<BasicBlock> blocks;
    }

    private static final EnumSet<IRInstruction.OpCode> CRITICAL_OPS = EnumSet.of(
        IRInstruction.OpCode.LABEL, IRInstruction.OpCode.GOTO,
        IRInstruction.OpCode.BREQ, IRInstruction.OpCode.BRNEQ,
        IRInstruction.OpCode.BRLT, IRInstruction.OpCode.BRGT,
        IRInstruction.OpCode.BRGEQ, IRInstruction.OpCode.RETURN,
        IRInstruction.OpCode.CALL, IRInstruction.OpCode.CALLR,
        IRInstruction.OpCode.ARRAY_STORE
    );

    // -------------------------------------------------------------------------
    // Main function w/ everything in it
    private static void optimizer(IRFunction function) {
        deadcodeElimination(function);
        boolean changed = copyPropagate(function);
        if (changed) {
            deadcodeElimination(function);
        }

        changed = constantFold(function);

        if (changed) {
            deadcodeElimination(function);
        }
    }

    // Deadcode Elimination
    private static void deadcodeElimination(IRFunction function) {
        List<IRInstruction> insts = function.instructions;
        int n = insts.size();

        ReachingDefsResult rdr = computeReachingDefs(insts);

        boolean[] marked = new boolean[n];
        ArrayDeque<Integer> worklist = new ArrayDeque<>();

        // mark critical insts first
        for (int i = 0; i < n; i++) {
            if (isCritical(insts.get(i))) {
                marked[i] = true;
                worklist.addLast(i);
            }
        }

        // propagate marks to reaching defs of used vars
        while (!worklist.isEmpty()) {
            int i = worklist.removeFirst();
            IRInstruction inst = insts.get(i);
            Set<String> usedVars = getUsedVariableNames(inst);

            for (String v : usedVars) {
                BitSet rd = rdr.reachingDefs[i];
                for (int d = rd.nextSetBit(0); d >= 0; d = rd.nextSetBit(d + 1)) {
                    String defVar = getDefinedVar(insts.get(rdr.defInst[d]));
                    if (v.equals(defVar)) {
                        int defI = rdr.defInst[d];
                        if (!marked[defI]) {
                            marked[defI] = true;
                            worklist.addLast(defI);
                        }
                    }
                }
            }
        }

        // sweep dead code
        List<IRInstruction> newInsts = new ArrayList<>();
        for (int i = 0; i < n; i++) {
            if (!marked[i] && isDeletableIfUnmarked(insts.get(i))) continue;
            newInsts.add(insts.get(i));
        }
        function.instructions = newInsts;
    }

    // copy propagation pass

    private static boolean copyPropagate(IRFunction f) {
        List<IRInstruction> insts = f.instructions;
        boolean anyChanged = false;

        ReachingDefsResult rdr = computeReachingDefs(insts);

        for (int copyIdx = 0; copyIdx < insts.size(); copyIdx++) {
            IRInstruction copyInst = insts.get(copyIdx);
            if (copyInst.opCode != IRInstruction.OpCode.ASSIGN) continue;
            if (copyInst.operands == null || copyInst.operands.length != 2) continue;
            if (!(copyInst.operands[0] instanceof IRVariableOperand)) continue;
            if (!(copyInst.operands[1] instanceof IRVariableOperand)) continue;

            IRVariableOperand dstOp = (IRVariableOperand) copyInst.operands[0];
            IRVariableOperand srcOp = (IRVariableOperand) copyInst.operands[1];

            if (dstOp.type instanceof IRArrayType || srcOp.type instanceof IRArrayType) continue;

            String dst = dstOp.getName();
            String src = srcOp.getName();
            if (dst.equals(src)) continue;

            int copyDefIdx = rdr.instDefIdx[copyIdx];
            if (copyDefIdx < 0) continue;

            List<Integer> srcDefList = rdr.varDefs.getOrDefault(src, Collections.emptyList());
            BitSet srcDefsAtCopy = new BitSet();
            for (int d : srcDefList) {
                if (rdr.reachingDefs[copyIdx].get(d)) {
                    srcDefsAtCopy.set(d);
                }
            }

            for (int i = 0; i < insts.size(); i++) {
                if (i == copyIdx) continue;
                IRInstruction inst = insts.get(i);
                Set<String> used = getUsedVariableNames(inst);
                if (!used.contains(dst)) continue;

                // only propagate if this is the sole reaching def of dst
                List<Integer> dstDefList = rdr.varDefs.getOrDefault(dst, Collections.emptyList());
                int dstDefsAtI = 0;
                for (int d : dstDefList) {
                    if (rdr.reachingDefs[i].get(d)) dstDefsAtI++;
                }
                if (dstDefsAtI != 1) continue;
                if (!rdr.reachingDefs[i].get(copyDefIdx)) continue;

                // also need to make sure src wasn't redefined
                BitSet srcDefsAtI = new BitSet();
                for (int d : srcDefList) {
                    if (rdr.reachingDefs[i].get(d)) {
                        srcDefsAtI.set(d);
                    }
                }
                if (!srcDefsAtCopy.equals(srcDefsAtI)) continue;

                replaceUseOfVar(inst, dst, src, srcOp.type);
                anyChanged = true;
            }
        }

        return anyChanged;
    }

    private static void replaceUseOfVar(IRInstruction inst, String oldName, String newName, IRType newType) {
        IRInstruction.OpCode op = inst.opCode;
        IROperand[] ops = inst.operands;
        if (ops == null) return;

        switch (op) {
            case ASSIGN:
                if (ops.length == 2) {
                    replaceAt(inst, ops, 1, oldName, newName, newType);
                } else if (ops.length == 3) {
                    // array write - replace idx and val
                    replaceAt(inst, ops, 1, oldName, newName, newType);
                    replaceAt(inst, ops, 2, oldName, newName, newType);
                }
                break;
            case ADD: case SUB: case MULT: case DIV: case AND: case OR:
            case BREQ: case BRNEQ: case BRLT: case BRGT: case BRGEQ:
                replaceAt(inst, ops, 1, oldName, newName, newType);
                replaceAt(inst, ops, 2, oldName, newName, newType);
                break;
            case RETURN:
                replaceAt(inst, ops, 0, oldName, newName, newType);
                break;
            case CALL:
                for (int i = 1; i < ops.length; i++)
                    replaceAt(inst, ops, i, oldName, newName, newType);
                break;
            case CALLR:
                for (int i = 2; i < ops.length; i++)
                    replaceAt(inst, ops, i, oldName, newName, newType);
                break;
            case ARRAY_STORE:
                replaceAt(inst, ops, 0, oldName, newName, newType);
                replaceAt(inst, ops, 2, oldName, newName, newType);
                break;
            case ARRAY_LOAD:
                replaceAt(inst, ops, 2, oldName, newName, newType);
                break;
            default:
                break;
        }
    }

    private static void replaceAt(IRInstruction inst, IROperand[] ops, int idx,
                                   String oldName, String newName, IRType newType) {
        if (idx >= ops.length) return;
        if (ops[idx] instanceof IRVariableOperand) {
            IRVariableOperand v = (IRVariableOperand) ops[idx];
            if (v.getName().equals(oldName)) {
                ops[idx] = new IRVariableOperand(newType, newName, inst);
            }
        }
    }

    // constant folding
    private static boolean constantFold(IRFunction f) {
        List<IRInstruction> insts = f.instructions;
        boolean anyChanged = false;

        for (int i = 0; i < insts.size(); i++) {
            IRInstruction inst = insts.get(i);
            IRInstruction.OpCode op = inst.opCode;
            IROperand[] ops = inst.operands;

            if (ops == null || ops.length < 3) continue;
            if (!(ops[0] instanceof IRVariableOperand)) continue;
            if (!(ops[1] instanceof IRConstantOperand)) continue;
            if (!(ops[2] instanceof IRConstantOperand)) continue;

            boolean isBinArith = op == IRInstruction.OpCode.ADD
                    || op == IRInstruction.OpCode.SUB
                    || op == IRInstruction.OpCode.MULT
                    || op == IRInstruction.OpCode.DIV
                    || op == IRInstruction.OpCode.AND
                    || op == IRInstruction.OpCode.OR;
            if (!isBinArith) continue;

            IRConstantOperand c1 = (IRConstantOperand) ops[1];
            IRConstantOperand c2 = (IRConstantOperand) ops[2];
            IRVariableOperand dst = (IRVariableOperand) ops[0];

            // only int - floats have formatting issues
            if (!(c1.type instanceof IRIntType) || !(c2.type instanceof IRIntType)) continue;

            long v1, v2;
            try {
                v1 = Long.parseLong(c1.getValueString());
                v2 = Long.parseLong(c2.getValueString());
            } catch (NumberFormatException e) {
                continue;
            }

            long result;
            switch (op) {
                case ADD:  result = v1 + v2; break;
                case SUB:  result = v1 - v2; break;
                case MULT: result = v1 * v2; break;
                case DIV:
                    if (v2 == 0) continue;
                    result = v1 / v2;
                    break;
                case AND: result = (v1 != 0 && v2 != 0) ? 1 : 0; break;
                case OR:  result = (v1 != 0 || v2 != 0) ? 1 : 0; break;
                default: continue;
            }

            IRInstruction newInst = new IRInstruction();
            newInst.opCode = IRInstruction.OpCode.ASSIGN;
            newInst.irLineNumber = inst.irLineNumber;
            IRVariableOperand dstNew = new IRVariableOperand(dst.type, dst.getName(), newInst);
            IRConstantOperand resultOp = new IRConstantOperand(IRIntType.get(), String.valueOf(result), newInst);
            newInst.operands = new IROperand[]{dstNew, resultOp};
            insts.set(i, newInst);
            anyChanged = true;
        }

        return anyChanged;
    }

    // reaching defs computation
    private static ReachingDefsResult computeReachingDefs(List<IRInstruction> insts) {
        int n = insts.size();

        // collect all defs first
        int[] instDefIdx = new int[n];
        Arrays.fill(instDefIdx, -1);
        Map<String, List<Integer>> varDefs = new HashMap<>();
        List<Integer> defInstList = new ArrayList<>();

        int numDefs = 0;
        for (int i = 0; i < n; i++) {
            String defVar = getDefinedVar(insts.get(i));
            if (defVar != null) {
                instDefIdx[i] = numDefs;
                defInstList.add(i);
                varDefs.computeIfAbsent(defVar, k -> new ArrayList<>()).add(numDefs);
                numDefs++;
            }
        }

        int[] defInst = new int[numDefs];
        for (int d = 0; d < numDefs; d++) {
            defInst[d] = defInstList.get(d);
        }

        // build the cfg - find leaders then create blocks
        boolean[] isLeader = new boolean[n];
        if (n > 0) isLeader[0] = true;

        for (int i = 0; i < n; i++) {
            IRInstruction.OpCode op = insts.get(i).opCode;
            if (op == IRInstruction.OpCode.LABEL) {
                isLeader[i] = true;
            }
            boolean isTerminator = op == IRInstruction.OpCode.GOTO
                    || op == IRInstruction.OpCode.BREQ  || op == IRInstruction.OpCode.BRNEQ
                    || op == IRInstruction.OpCode.BRLT  || op == IRInstruction.OpCode.BRGT
                    || op == IRInstruction.OpCode.BRGEQ || op == IRInstruction.OpCode.RETURN;
            if (isTerminator && i + 1 < n) {
                isLeader[i + 1] = true;
            }
        }

        List<BasicBlock> blocks = new ArrayList<>();
        Map<String, Integer> labelToBlock = new HashMap<>();

        int blockStart = -1;
        for (int i = 0; i < n; i++) {
            if (isLeader[i]) {
                if (blockStart >= 0) {
                    BasicBlock bb = new BasicBlock();
                    bb.id = blocks.size();
                    bb.start = blockStart;
                    bb.end = i - 1;
                    blocks.add(bb);
                }
                blockStart = i;
            }
        }
        if (blockStart >= 0 && n > 0) {
            BasicBlock bb = new BasicBlock();
            bb.id = blocks.size();
            bb.start = blockStart;
            bb.end = n - 1;
            blocks.add(bb);
        }

        for (BasicBlock bb : blocks) {
            IRInstruction first = insts.get(bb.start);
            if (first.opCode == IRInstruction.OpCode.LABEL
                    && first.operands != null && first.operands.length > 0) {
                labelToBlock.put(first.operands[0].toString(), bb.id);
            }
        }

        // wire up successors/predecessors
        for (BasicBlock bb : blocks) {
            IRInstruction last = insts.get(bb.end);
            IRInstruction.OpCode op = last.opCode;
            IROperand[] ops = last.operands;

            if (op == IRInstruction.OpCode.GOTO) {
                if (ops != null && ops.length > 0) {
                    Integer target = labelToBlock.get(ops[0].toString());
                    if (target != null) {
                        bb.succs.add(target);
                        blocks.get(target).preds.add(bb.id);
                    }
                }
            } else if (op == IRInstruction.OpCode.BREQ  || op == IRInstruction.OpCode.BRNEQ
                    || op == IRInstruction.OpCode.BRLT  || op == IRInstruction.OpCode.BRGT
                    || op == IRInstruction.OpCode.BRGEQ) {
                if (ops != null && ops.length > 0) {
                    Integer target = labelToBlock.get(ops[0].toString());
                    if (target != null) {
                        bb.succs.add(target);
                        blocks.get(target).preds.add(bb.id);
                    }
                }
                // fall through
                if (bb.id + 1 < blocks.size()) {
                    bb.succs.add(bb.id + 1);
                    blocks.get(bb.id + 1).preds.add(bb.id);
                }
            } else if (op == IRInstruction.OpCode.RETURN) {
                // terminal
            } else {
                if (bb.id + 1 < blocks.size()) {
                    bb.succs.add(bb.id + 1);
                    blocks.get(bb.id + 1).preds.add(bb.id);
                }
            }
        }

        // gen/kill for each block
        for (BasicBlock bb : blocks) {
            bb.gen  = new BitSet(numDefs);
            bb.kill = new BitSet(numDefs);
            bb.in   = new BitSet(numDefs);
            bb.out  = new BitSet(numDefs);

            Map<String, List<Integer>> blockVarDefs = new HashMap<>();
            for (int i = bb.start; i <= bb.end; i++) {
                int d = instDefIdx[i];
                if (d < 0) continue;
                String v = getDefinedVar(insts.get(i));
                blockVarDefs.computeIfAbsent(v, k -> new ArrayList<>()).add(d);
            }

            for (String v : blockVarDefs.keySet()) {
                List<Integer> allDefsOfV = varDefs.getOrDefault(v, Collections.emptyList());
                List<Integer> blockDefsOfV = blockVarDefs.get(v);
                for (int d : allDefsOfV) {
                    if (!blockDefsOfV.contains(d)) bb.kill.set(d);
                }
            }

            // forward scan - last def of each var is the one that survives
            for (int i = bb.start; i <= bb.end; i++) {
                int d = instDefIdx[i];
                if (d < 0) continue;
                String v = getDefinedVar(insts.get(i));
                List<Integer> allDefsOfV = varDefs.getOrDefault(v, Collections.emptyList());
                for (int od : allDefsOfV) bb.gen.clear(od);
                bb.gen.set(d);
            }
        }

        // iterate until fixpoint
        boolean changed = true;
        while (changed) {
            changed = false;
            for (BasicBlock bb : blocks) {
                BitSet newIn = new BitSet(numDefs);
                for (int predId : bb.preds) {
                    newIn.or(blocks.get(predId).out);
                }

                BitSet newOut = (BitSet) newIn.clone();
                newOut.andNot(bb.kill);
                newOut.or(bb.gen);

                if (!newOut.equals(bb.out) || !newIn.equals(bb.in)) {
                    bb.in = newIn;
                    bb.out = newOut;
                    changed = true;
                }
            }
        }

        // get per-instruction reaching defs from block-level results
        BitSet[] reachingDefs = new BitSet[n];
        for (BasicBlock bb : blocks) {
            BitSet running = (BitSet) bb.in.clone();
            for (int i = bb.start; i <= bb.end; i++) {
                reachingDefs[i] = (BitSet) running.clone();

                int d = instDefIdx[i];
                if (d >= 0) {
                    String v = getDefinedVar(insts.get(i));
                    List<Integer> allDefsOfV = varDefs.getOrDefault(v, Collections.emptyList());
                    for (int od : allDefsOfV) running.clear(od);
                    running.set(d);
                }
            }
        }

        for (int i = 0; i < n; i++) {
            if (reachingDefs[i] == null) reachingDefs[i] = new BitSet(numDefs);
        }

        ReachingDefsResult result = new ReachingDefsResult();
        result.numDefs = numDefs;
        result.defInst = defInst;
        result.instDefIdx = instDefIdx;
        result.varDefs = varDefs;
        result.reachingDefs = reachingDefs;
        result.blocks = blocks;
        return result;
    }

    // helpers

    // what variable does this inst define? null if it doesn't define one
    private static String getDefinedVar(IRInstruction inst) {
        IRInstruction.OpCode op = inst.opCode;
        IROperand[] ops = inst.operands;
        if (ops == null || ops.length == 0) return null;

        switch (op) {
            case ASSIGN:
                if (ops.length == 2 && ops[0] instanceof IRVariableOperand)
                    return ((IRVariableOperand) ops[0]).getName();
                return null;
            case ADD: case SUB: case MULT: case DIV: case AND: case OR:
            case ARRAY_LOAD:
            case CALLR:
                if (ops[0] instanceof IRVariableOperand)
                    return ((IRVariableOperand) ops[0]).getName();
                return null;
            default:
                return null;
        }
    }

    private static boolean isCritical(IRInstruction inst) {
        if (CRITICAL_OPS.contains(inst.opCode)) return true;
        // 3-operand assign = array element write
        if (inst.opCode == IRInstruction.OpCode.ASSIGN
                && inst.operands != null && inst.operands.length == 3)
            return true;
        return false;
    }

    private static Set<String> getUsedVariableNames(IRInstruction inst) {
        Set<String> used = new HashSet<>();
        IRInstruction.OpCode op = inst.opCode;
        IROperand[] ops = inst.operands;
        if (ops == null) return used;

        switch (op) {
            case ASSIGN:
                if (ops.length == 2) {
                    addIfVar(used, ops[1]);
                } else if (ops.length == 3) {
                    addIfVar(used, ops[1]);
                    addIfVar(used, ops[2]);
                }
                break;
            case ADD: case SUB: case MULT: case DIV: case AND: case OR:
            case BREQ: case BRNEQ: case BRLT: case BRGT: case BRGEQ:
                if (ops.length >= 3) {
                    addIfVar(used, ops[1]);
                    addIfVar(used, ops[2]);
                }
                break;
            case RETURN:
                if (ops.length >= 1) addIfVar(used, ops[0]);
                break;
            case CALL:
                for (int i = 1; i < ops.length; i++) addIfVar(used, ops[i]);
                break;
            case CALLR:
                for (int i = 2; i < ops.length; i++) addIfVar(used, ops[i]);
                break;
            case ARRAY_STORE:
                if (ops.length >= 3) {
                    addIfVar(used, ops[0]);
                    addIfVar(used, ops[2]);
                }
                break;
            case ARRAY_LOAD:
                if (ops.length >= 3) addIfVar(used, ops[2]);
                break;
            default:
                break;
        }
        return used;
    }

    // small helper to cut down on the instanceof boilerplate
    private static void addIfVar(Set<String> set, IROperand operand) {
        if (operand instanceof IRVariableOperand)
            set.add(((IRVariableOperand) operand).getName());
    }

    // inverse of isCritical basically - can we safely remove this?
    private static boolean isDeletableIfUnmarked(IRInstruction inst) {
        if (isCritical(inst)) return false;
        switch (inst.opCode) {
            case ASSIGN: return inst.operands != null && inst.operands.length == 2;
            case ADD: case SUB: case MULT: case DIV:
            case AND: case OR: case ARRAY_LOAD:
                return true;
            default: return false;
        }
    }
}