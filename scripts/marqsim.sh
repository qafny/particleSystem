#!/bin/bash

python3 scripts/qblue_bench.py \
  --dataset all \
  --out "results/marqsim_genesis.csv" \
  --errs 0.5 \
  --ts 0.01 \
  --pipelines std qdrift \
  --grouping none \
  --timeout-s 1800