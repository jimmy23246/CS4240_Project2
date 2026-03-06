#!/bin/bash
set -euo pipefail

# build output dir
mkdir -p build

# compile everything (helper + optimizer)
javac -d build \
  $(find materials/src -name "*.java") \
  $(find src -name "*.java")