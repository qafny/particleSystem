#!/bin/bash

cd ../
coq_makefile -f _CoqProject -o Makefile
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
rm -f Bin* ClassicalDedekindReals.ml ConstructiveCauchyReals.ml Nat0.ml \
   QArith_base.ml Rdefinitions.ml Ring_theory.ml Rpow_def.ml Rtrigo1.ml \
   Specif.ml ZArith_dec.ml

# Move the remaining extracted files to the 'ml' subdirectory.
echo "Moving generated files to ml/..."
mv *.ml ml
