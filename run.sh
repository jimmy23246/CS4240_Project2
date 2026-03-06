#!/bin/bash
set -euo pipefail

if [ $# -ne 2 ]; then
  echo "Usage: ./run.sh <input.ir> <output.ir>" >&2
  exit 1
fi

INPUT_IR="$1"
OUTPUT_IR="$2"

java -cp build OptimizerMain "$INPUT_IR" "$OUTPUT_IR"