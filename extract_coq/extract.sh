#!/bin/bash

# dir of qblue coq project
dir_src="src"
PYTHON3_BIN="${PYTHON3_BIN:-python3}"

# All other dirs are relative to src
dir_coq="../../coq" # relative to the dir of Extract.v

# dir of the extracted ml
dir_ml_ori=extracted
dir_ml="../ml"

# root modules to extract
modules="QBlueCompile"


cd $dir_src

# Ensure output directories exist (Coq extraction fails if missing).
mkdir -p "$dir_ml_ori" "$dir_ml"

# make coq project first
cd $dir_coq
make
cd -

# Perform extraction.
echo "Extracting code..."
coqc -R $dir_coq QBlue Extraction.v

# Move the remaining extracted files to the 'ml' subdirectory.
echo "Moving generated files to ml..."
"$PYTHON3_BIN" prune.py $dir_ml_ori $dir_ml $modules
cp ./networks/* $dir_ml
 
