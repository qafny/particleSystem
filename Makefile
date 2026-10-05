.DEFAULT_GOAL := all

PYTHON ?= $(CURDIR)/.venv/bin/python
WORKERS ?= 8

.PHONY: all qblue phoenix openfermion thirdparty plot clean

# Keep plotting after all experiments, including when make uses -j.
all: qblue
	$(MAKE) thirdparty
	$(MAKE) plot

qblue:
	cd mlqblue && dune build performance.exe
	mkdir -p results
	cd mlqblue && "$(PYTHON)" gen_result_threaded.py --input job.csv --output ../results/qblue_results.csv --workers $(WORKERS)

# Standalone baseline targets reuse existing QBlue results, or create them.
results/qblue_results.csv:
	$(MAKE) qblue

phoenix: results/qblue_results.csv
	"$(PYTHON)" scripts/benchmark_threaded.py --compiler phoenix --workers $(WORKERS)

openfermion: results/qblue_results.csv
	"$(PYTHON)" scripts/benchmark_threaded.py --compiler openfermion --workers $(WORKERS)

thirdparty: phoenix openfermion

plot:
	"$(PYTHON)" scripts/plot_results.py

clean:
	rm -rf mlqblue/_build mlqblue/__pycache__ scripts/__pycache__ results/plots
	rm -f results/qblue_results.csv results/phoenix_results.csv results/openfermion_results.csv
	rm -f results/.qblue_results.* results/.qblue_results.csv.*.tmp results/.phoenix_results.csv.*.tmp results/.openfermion_results.csv.*.tmp
