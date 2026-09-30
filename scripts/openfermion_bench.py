#!/usr/bin/env python3
"""OpenFermion second-order benchmark with gen_result.py-compatible CSV output.

Run from mlqblue: python3 ../scripts/openfermion_bench.py -i job.csv -o result_openfermion.csv
The companion .metadata.jsonl records the leading-order BCH error model; it is
not a certificate bounding the omitted higher-order remainder.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
import os
import re
import subprocess
import sys
import time
import tempfile
from importlib.metadata import version
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT / 'mlqblue'))
from gen_result import CSV_FIELDS

VENDOR = ROOT / 'thirdparty' / 'OpenFermion'
MARQ = re.compile(r'^\s*([+-]?)\s*((?:\d+(?:\.\d*)?|\.\d+)(?:[eE][-+]?\d+)?)\s*\*\s*([IXYZ]+)\s*$')
GENESIS = re.compile(r'^\s*([IXYZ]+)\s+\(([^)]+)\)\s*$')


def parse_hamiltonian(path):
    """Reject malformed terms rather than silently changing the Hamiltonian."""
    terms = []
    for number, line in enumerate(path.read_text().splitlines(), 1):
        if not line.strip() or line.lstrip().startswith('#'):
            continue
        m = MARQ.fullmatch(line)
        g = GENESIS.fullmatch(line)
        if m:
            sign, value, label = m.groups()
            coefficient = complex(float(value) * (-1 if sign == '-' else 1))
        elif g:
            label, value = g.groups()
            coefficient = complex(value.replace(' ', ''))
        else:
            raise ValueError(f'{path}:{number}: unrecognized Hamiltonian term')
        if not math.isfinite(coefficient.real) or coefficient.imag != 0:
            raise ValueError(f'{path}:{number}: expected finite real coefficient')
        terms.append((label, coefficient.real))
    if not terms or any(len(p) != len(terms[0][0]) for p, _ in terms):
        raise ValueError('Empty Hamiltonian or inconsistent Pauli-string lengths')
    return terms


def gate_counts(qc):
    return (sum(i.operation.num_qubits == 1 for i in qc.data),
            sum(i.operation.num_qubits >= 2 for i in qc.data))


def benchmark(row, meta, args):
    os.environ.setdefault('MPLCONFIGDIR', str(Path(tempfile.gettempdir()) / 'particleSystem_openfermion_mplconfig'))
    from openfermion import QubitOperator, trotterize_exp_qubop_to_qasm
    from openfermion.circuits.trotter.trotter_error import error_bound, trotter_steps_required_propagator
    from qiskit import QuantumCircuit, transpile

    meta['versions'] = {name: version(name) for name in ('openfermion', 'qiskit', 'numpy', 'scipy')}

    tolerance, duration = float(row['error']), float(row['time'])
    if not math.isfinite(tolerance) or tolerance <= 0 or not math.isfinite(duration):
        raise ValueError('error must be finite and positive; time must be finite')
    path = Path(row['file_name'])  # Same working-directory convention as gen_result.py.
    parsed = parse_hamiltonian(path)
    row.update(nqubit=len(parsed[0][0]), program_size=len(parsed))
    meta['input_sha256'] = hashlib.sha256(path.read_bytes()).hexdigest()
    op = QubitOperator()
    for label, coefficient in parsed:
        op += QubitOperator(tuple((i, p) for i, p in enumerate(label) if p != 'I'), coefficient)
    identity = float(op.terms.pop((), 0))
    op.terms = {p: c for p, c in op.terms.items() if c != 0}
    order = sorted(op.terms)
    if args.max_terms and len(order) > args.max_terms:
        raise ValueError(f'{len(order)} terms exceeds --max-terms={args.max_terms}')
    # error_operator indexes a reverse/forward symmetric product. The gate
    # stream uses forward/reverse order, so reverse its list for the bound.
    bound_start = time.perf_counter()
    bound = float(error_bound([QubitOperator(p, op.terms[p]) for p in reversed(order)], tight=args.tight)) if duration else 0.0
    if not math.isfinite(bound) or bound < 0:
        raise ValueError('Non-finite or negative bound coefficient')
    steps = trotter_steps_required_propagator(bound, duration, tolerance) if order else 0
    expanded = (2 * len(order) - 1) * steps if len(order) > 1 else len(order) * steps
    meta.update(bound_coefficient=bound, bound_seconds=time.perf_counter()-bound_start,
                predicted_error=bound * abs(duration)**3 / steps**2 if steps else 0,
                effective_terms=len(order), identity_coefficient=identity,
                term_ordering=[list(p) for p in order])
    row['trotter_step'] = steps
    row['compilation_terms'] = expanded
    if args.max_exponentials and expanded > args.max_exponentials:
        raise ValueError(f'{expanded} exponentials exceeds --max-exponentials={args.max_exponentials}')
    start = time.perf_counter()
    qc = QuantumCircuit(row['nqubit'])
    qc.global_phase = -identity * duration
    if steps:
        lines = trotterize_exp_qubop_to_qasm(op, evolution_time=duration,
            trotter_number=steps, trotter_order=2 if len(order) > 1 else 1,
            term_ordering=order)
        for line in lines:
            parts = line.split()
            gate = parts[0]
            if gate == 'H': qc.h(int(parts[1]))
            elif gate == 'Rx': qc.rx(float(parts[1]), int(parts[2]))
            elif gate == 'Rz': qc.rz(float(parts[1]), int(parts[2]))
            elif gate == 'CNOT': qc.cx(int(parts[1]), int(parts[2]))
            else: raise ValueError(f'Unsupported gate: {line}')
    basis = ['u1', 'u2', 'u3', 'cx']
    before = transpile(qc, basis_gates=basis, optimization_level=0, seed_transpiler=0)
    after = transpile(before, basis_gates=basis, optimization_level=3, seed_transpiler=0)
    row['compilation_time'] = time.perf_counter() - start
    row['single_qubit_gates_bfopt'], row['multi_qubit_gates_bfopt'] = gate_counts(before)
    row['single_qubit_gates'], row['multi_qubit_gates'] = gate_counts(after)
    return qc


def build_parser():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('-i', '--input', type=Path, required=True)
    ap.add_argument('-o', '--output', type=Path, default=Path('result_openfermion.csv'))
    ap.add_argument('-e', '--error', type=float, default=0.1)
    ap.add_argument('-t', '--time', type=float, default=0.7854)
    ap.add_argument('-p', '--path-flag', type=int, default=2)
    ap.add_argument('--tight', action='store_true', help='Use coefficient 1-norm of BCH error operator (potentially cubic cost).')
    ap.add_argument('--max-terms', type=int, default=5000, help='Bound-computation term limit; 0 disables.')
    ap.add_argument('--max-exponentials', type=int, default=1000000, help='Circuit expansion limit; 0 disables.')
    return ap


def main():
    ap = build_parser()
    args = ap.parse_args()
    if args.max_terms < 0 or args.max_exponentials < 0:
        ap.error('Limits must be nonnegative')
    if args.input.resolve() == args.output.resolve():
        ap.error('Input and output must differ')
    if not (VENDOR / 'src/openfermion').is_dir():
        ap.error(f'Missing OpenFermion checkout: {VENDOR}')
    sys.path.insert(0, str(VENDOR / 'src'))
    revision = subprocess.run(['git', '-C', str(VENDOR), 'rev-parse', 'HEAD'], capture_output=True, text=True).stdout.strip()
    metadata_path = args.output.with_suffix(args.output.suffix + '.metadata.jsonl')
    failures = 0
    with args.input.open(newline='') as source:
        reader = csv.DictReader(source)
        if not reader.fieldnames or 'file_name' not in reader.fieldnames:
            ap.error("Input CSV must contain 'file_name'")
        args.output.parent.mkdir(parents=True, exist_ok=True)
        with args.output.open('w', newline='') as out, metadata_path.open('w') as metadata:
            writer = csv.DictWriter(out, fieldnames=CSV_FIELDS)
            writer.writeheader()
            for index, job in enumerate(reader, 2):
                if not (job.get('file_name') or '').strip(): continue
                row = dict.fromkeys(CSV_FIELDS, '')
                row.update(file_name=job['file_name'].strip(),
                    error=(job.get('error') or '').strip() or args.error,
                    time=(job.get('time') or '').strip() or args.time,
                    path_flag=(job.get('path_flag') or '').strip() or args.path_flag)
                meta = dict(csv_line=index, compiler='openfermion', revision=revision,
                    bound_method='tight' if args.tight else 'loose',
                    error_model='leading-order BCH propagator estimate B*abs(t)^3/r^2; higher-order remainder not certified',
                    compilation_time_scope='gate generation plus basis conversion and optimization; excludes parsing and bound computation')
                try:
                    flag = int(row['path_flag'])
                    if flag != 2:
                        row.update(status='unsupported', message='Only path_flag=2 (second-order digital Trotter) is supported')
                    else:
                        benchmark(row, meta, args)
                        row.update(status='ok', message='')
                except Exception as exc:
                    failures += 1
                    row.update(status='error', message=str(exc))
                writer.writerow(row)
                meta.update(result=row)
                metadata.write(json.dumps(meta, allow_nan=False) + '\n')
                out.flush(); metadata.flush()
                print(f"{row['status']}: {row['file_name']} path={row['path_flag']} {row['message']}", flush=True)
    print(f'Saved {args.output} and {metadata_path}')
    return 1 if failures else 0


if __name__ == '__main__':
    raise SystemExit(main())
