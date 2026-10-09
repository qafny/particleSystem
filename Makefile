.DEFAULT_GOAL := all

PYTHON ?= $(CURDIR)/.venv/bin/python
WORKERS ?= 8
# performance.exe options for every job: all-to-all target, sorted Trotter terms
QBLUE_FLAGS ?= -arch a2a -sort
export QBLUE_FLAGS

.PHONY: all build extract qblue phoenix openfermion thirdparty bounds tables plot clean

# Keep plotting after all experiments, including when make uses -j.
all: qblue
	$(MAKE) thirdparty
	$(MAKE) bounds
	$(MAKE) tables
	$(MAKE) plot

# Coq proofs -> OCaml extraction -> mlqblue/qbluelib
extract:
	cd extract_coq && bash extract.sh
	rm -f mlqblue/qbluelib/*.ml
	cp extract_coq/ml/*.ml mlqblue/qbluelib/

build:
	cd mlqblue && dune build performance.exe

qblue: build
	mkdir -p results
	cd mlqblue && "$(PYTHON)" gen_result_threaded.py --input job.csv --output ../results/qblue_results.csv --workers $(WORKERS) --allow-job-errors

# Standalone baseline targets reuse existing QBlue results, or create them.
results/qblue_results.csv:
	$(MAKE) qblue

phoenix: results/qblue_results.csv
	"$(PYTHON)" scripts/benchmark_threaded.py --compiler phoenix --workers $(WORKERS) --allow-job-errors

openfermion: results/qblue_results.csv
	"$(PYTHON)" scripts/benchmark_threaded.py --compiler openfermion --workers $(WORKERS) --allow-job-errors

thirdparty: phoenix openfermion

bounds: results/qblue_results.csv
	"$(PYTHON)" scripts/bounds.py --workers $(WORKERS)

tables:
	"$(PYTHON)" scripts/tables.py

plot:
	"$(PYTHON)" scripts/plot_results.py

clean:
	rm -rf mlqblue/_build mlqblue/__pycache__ scripts/__pycache__ results/plots
	rm -f results/qblue_results.csv results/phoenix_results.csv results/openfermion_results.csv
	rm -f results/bounds_results.csv results/tables.md
	rm -f results/.qblue_results.* results/.qblue_results.csv.*.tmp results/.phoenix_results.csv.*.tmp results/.openfermion_results.csv.*.tmp
