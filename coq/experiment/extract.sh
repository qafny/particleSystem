#!/bin/bash

cd ../
coq_makefile -f _CoqProject -o Makefile
make clean
make

# Change into the extraction directory.
cd experiment/extraction

# Perform extraction.
echo "Extracting code..."
coqc -R ../.. QBlue Extraction.v

# Remove unneeded files.
echo "Deleting unneeded files..."
rm -f *.glob *.mli *.vo*

# Remove empty/unused files.
 rm -f  ClassicalDedekindReals.ml ConstructiveCauchyReals.ml Nat0.ml \
   Rpow_def.ml Rtrigo1.ml \
   ZArith_dec.ml Ring_theory.ml QArith_base.ml Rdefinitions.ml Specif.ml 

# Move the remaining extracted files to the 'ml' subdirectory.
echo "Moving generated files to ml/..."
for f in *.ml; do
  [ "$f" != "Run.ml" ] && mv "$f" ml/
done

echo "Building extracted code..."
dune build run.exe


