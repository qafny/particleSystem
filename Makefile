.DEFAULT_GOAL := all

PYTHON ?= $(CURDIR)/.venv/bin/python
WORKERS ?= 8
# RESUME=1 keeps finished jobs in results/qblue_results.csv and runs the rest
RESUME ?=
# performance.exe options for every job: all-to-all target, sorted Trotter terms
QBLUE_FLAGS ?= -arch a2a -sort
export QBLUE_FLAGS

# PennyLane baseline for the LCU run; its own environment, kept out of .venv
PL_PYTHON ?= $(HOME)/pl-venv/bin/python

.PHONY: all build extract qblue lcu grid ctime check-lcu qsvt-phases pennylane pennylane-short pennylane-angles angle-bench pennylane-tables paper phoenix openfermion thirdparty bounds tables plot clean

# Keep plotting after all experiments, including when make uses -j.
all: qblue
	$(MAKE) thirdparty
	$(MAKE) bounds
	$(MAKE) plot

# Coq proofs -> OCaml extraction -> mlqblue/qbluelib
extract:
	cd extract_coq && bash extract.sh
	rm -f mlqblue/qbluelib/*.ml
	cp extract_coq/ml/*.ml mlqblue/qbluelib/

build:
	cd mlqblue && dune build performance.exe lcucheck/lcucheck.exe phasecheck/phasecheck.exe

qblue: build
	mkdir -p results
	cd mlqblue && "$(PYTHON)" gen_result_threaded.py --input job.csv --output ../results/qblue_results.csv --workers $(WORKERS) --allow-job-errors $(if $(RESUME),--resume)

# LCU vs Trotter-based at tighter errors and longer times (mlqblue/job_lcu.csv)
lcu: build
	mkdir -p results
	cd mlqblue && "$(PYTHON)" gen_result_threaded.py --input job_lcu.csv --output ../results/lcu_results.csv --workers $(WORKERS) --allow-job-errors $(if $(RESUME),--resume)

# The rest of the 4 t x 4 eps grid that job.csv and job_lcu.csv leave out: every path at
# pi/16 and pi/4 with eps = 0.002 and 0.0002, QSVT again at pi/16 and pi/4, and the
# Indiana analog paths at pi and 4pi (mlqblue/job_grid.csv)
grid: build
	mkdir -p results
	cd mlqblue && "$(PYTHON)" gen_result_threaded.py --input job_grid.csv --output ../results/grid_extra.csv --workers $(WORKERS) --allow-job-errors $(if $(RESUME),--resume)

# Real QSP compile times with the piece cache off (mlqblue/job_ctime.csv): the programs
# PennyLane can build at pi/16, pi/4 and pi, and every program at 4pi
ctime: build
	mkdir -p results
	cd mlqblue && QBLUE_LCU_CACHE= "$(PYTHON)" gen_result_threaded.py --input job_ctime.csv --output ../results/ctime.csv --workers $(WORKERS) --allow-job-errors $(if $(RESUME),--resume)

# LCU circuits against exact evolution, and resource pieces against full circuits
check-lcu: build
	"$(PYTHON)" scripts/check_lcu.py --counts

# QSVT phases of every benchmark circuit (path 8 of job_lcu.csv) against their targets
qsvt-phases: build
	mkdir -p results
	"$(PYTHON)" scripts/check_qsvt_phases.py

# PennyLane GQSP + qubitization on the same programs, errors and times as `lcu`
pennylane:
	mkdir -p results
	"$(PL_PYTHON)" -W ignore scripts/pennylane_lcu.py --input mlqblue/job_lcu.csv --output results/pennylane_lcu.csv --workers $(WORKERS)

# PennyLane at pi/16 and pi/4 (mlqblue/job_pl_short.csv), plus its angle solver on them
pennylane-short:
	mkdir -p results
	"$(PL_PYTHON)" -W ignore scripts/pennylane_lcu.py --input mlqblue/job_pl_short.csv --output results/pennylane_lcu_short.csv --workers $(WORKERS)
	"$(PL_PYTHON)" -W ignore scripts/pennylane_angle_stats.py --input results/pennylane_lcu_short.csv --output results/pennylane_angle_stats_short.csv --workers $(WORKERS)

# PennyLane's angle solver on every setting's polynomial (needs results/pennylane_lcu.csv)
pennylane-angles: results/pennylane_lcu.csv
	"$(PL_PYTHON)" -W ignore scripts/pennylane_angle_stats.py --workers $(WORKERS)

results/pennylane_lcu.csv:
	$(MAKE) pennylane

# PennyLane's GQSP solver and QBlue's complement against degree
angle-bench:
	mkdir -p results
	: > results/angle_solver_benchmark.jsonl
	for tau in 5 10 25 50 100 200 300 400 800 1600; do timeout 1200 "$(PL_PYTHON)" -W ignore scripts/angle_solver_bench.py pl $$tau >> results/angle_solver_benchmark.jsonl || echo "{\"who\":\"pl\",\"tau\":$$tau,\"timeout\":1200}" >> results/angle_solver_benchmark.jsonl; done
	for tau in 5 10 25 50 100; do timeout 1200 "$(PL_PYTHON)" -W ignore scripts/angle_solver_bench.py ours $$tau >> results/angle_solver_benchmark.jsonl || echo "{\"who\":\"ours\",\"tau\":$$tau,\"timeout\":1200}" >> results/angle_solver_benchmark.jsonl; done

# QBlue LCU against PennyLane (needs results/lcu_results.csv and results/pennylane_lcu.csv)
pennylane-tables:
	"$(PYTHON)" scripts/pennylane_tables.py

# Paper tables and figures (results/paper/) from whatever of the runs above exist
paper:
	"$(PYTHON)" scripts/paper/paper_figs.py
	"$(PYTHON)" scripts/paper/pl_reliability.py
	"$(PYTHON)" scripts/paper/compile_time.py
	"$(PYTHON)" scripts/paper/analog_tables.py

# Standalone baseline targets reuse existing QBlue results, or create them.
results/qblue_results.csv:
	$(MAKE) qblue

phoenix: results/qblue_results.csv
	"$(PYTHON)" scripts/benchmark_threaded.py --compiler phoenix --workers $(WORKERS) --allow-job-errors $(if $(RESUME),--resume)

openfermion: results/qblue_results.csv
	"$(PYTHON)" scripts/benchmark_threaded.py --compiler openfermion --workers $(WORKERS) --allow-job-errors $(if $(RESUME),--resume)

thirdparty: phoenix openfermion

bounds: results/qblue_results.csv
	"$(PYTHON)" scripts/bounds.py --workers $(WORKERS)

tables:
	"$(PYTHON)" scripts/tables.py

plot: tables
	"$(PYTHON)" scripts/plot_results.py

clean:
	rm -rf mlqblue/_build mlqblue/__pycache__ scripts/__pycache__ scripts/paper/__pycache__ results/plots
	rm -f results/qblue_results.csv results/lcu_results.csv results/phoenix_results.csv results/openfermion_results.csv
	rm -f results/bounds_results.csv results/tables.md results/tables.tex results/savings.csv
	rm -f results/.qblue_results.* results/.qblue_results.csv.*.tmp results/.phoenix_results.csv.*.tmp results/.openfermion_results.csv.*.tmp
