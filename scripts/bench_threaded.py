#!/usr/bin/env python3
"""Run OpenFermion CSV jobs concurrently, one independent process per job."""

import csv
from concurrent.futures import ThreadPoolExecutor, as_completed
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
import openfermion_bench as bench


def positive_int(value):
    import argparse
    value = int(value)
    if value < 1:
        raise argparse.ArgumentTypeError('workers must be at least 1')
    return value


def run_job(job, args):
    """Delegate all bound and circuit calculations to the serial runner."""
    index, inputs = job
    row = dict.fromkeys(bench.CSV_FIELDS, '')
    row.update(inputs)
    meta = dict(csv_line=index, compiler='openfermion', workers=args.workers)
    try:
        with tempfile.TemporaryDirectory(prefix='openfermion-job-') as directory:
            source = Path(directory) / 'job.csv'
            output = Path(directory) / 'result.csv'
            with source.open('w', newline='') as handle:
                writer = csv.DictWriter(handle, fieldnames=list(inputs))
                writer.writeheader()
                writer.writerow(inputs)
            command = [sys.executable, str(Path(bench.__file__).resolve()),
                       '-i', str(source), '-o', str(output),
                       '--max-terms', str(args.max_terms),
                       '--max-exponentials', str(args.max_exponentials)]
            if args.tight:
                command.append('--tight')
            # Each worker has a separate interpreter; avoid nested library pools.
            env = os.environ.copy()
            env.update(OMP_NUM_THREADS='1', OPENBLAS_NUM_THREADS='1',
                       MKL_NUM_THREADS='1', QISKIT_PARALLEL='FALSE',
                       PYTHONDONTWRITEBYTECODE='1')
            proc = subprocess.run(command, capture_output=True, text=True, env=env)
            if not output.is_file():
                raise RuntimeError(proc.stderr.strip() or proc.stdout.strip() or
                                   f'Worker exited with code {proc.returncode}')
            with output.open(newline='') as handle:
                results = list(csv.DictReader(handle))
            metadata = [json.loads(line) for line in
                        Path(str(output) + '.metadata.jsonl').read_text().splitlines()]
            if len(results) != 1 or len(metadata) != 1:
                raise RuntimeError('Worker did not produce exactly one result and metadata record')
            row = results[0]
            meta = metadata[0]
            if proc.returncode and row['status'] != 'error':
                raise RuntimeError(proc.stderr.strip() or f'Worker exited with code {proc.returncode}')
    except Exception as exc:
        row.update(status='error', message=str(exc))
    meta.update(csv_line=index, workers=args.workers, result=row)
    return row, meta


def atomic_write(path, write):
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(mode='w', newline='', encoding='utf-8',
                dir=path.parent, prefix=f'.{path.name}.', suffix='.tmp', delete=False) as handle:
            temporary = Path(handle.name)
            write(handle)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def save_results(output, results):
    """Save completed jobs in input order; each output file is replaced atomically."""
    def write_csv(handle):
        writer = csv.DictWriter(handle, fieldnames=bench.CSV_FIELDS)
        writer.writeheader()
        writer.writerows(result[0] for result in results if result is not None)

    def write_metadata(handle):
        for result in results:
            if result is not None:
                handle.write(json.dumps(result[1], allow_nan=False) + '\n')

    atomic_write(Path(str(output) + '.metadata.jsonl'), write_metadata)
    atomic_write(output, write_csv)


def main():
    parser = bench.build_parser()
    parser.description = __doc__
    parser.set_defaults(output=Path('result_openfermion_threaded.csv'))
    parser.add_argument('-w', '--workers', type=positive_int, default=1,
                        help='Concurrent OpenFermion processes (default: 1).')
    args = parser.parse_args()
    if args.max_terms < 0 or args.max_exponentials < 0:
        parser.error('Limits must be nonnegative')
    metadata_path = Path(str(args.output) + '.metadata.jsonl')
    if args.input.resolve() in (args.output.resolve(), metadata_path.resolve()):
        parser.error('Input and output paths must differ')
    if not (bench.VENDOR / 'src/openfermion').is_dir():
        parser.error(f'Missing OpenFermion checkout: {bench.VENDOR}')
    jobs = []
    with args.input.open(newline='') as handle:
        reader = csv.DictReader(handle)
        if not reader.fieldnames or 'file_name' not in reader.fieldnames:
            parser.error("Input CSV must contain 'file_name'")
        for index, item in enumerate(reader, 2):
            if not (item.get('file_name') or '').strip():
                continue
            inputs = dict(file_name=item['file_name'].strip())
            for field, default in [('error', args.error), ('time', args.time),
                                   ('path_flag', args.path_flag)]:
                inputs[field] = (item.get(field) or '').strip() or default
            jobs.append((index, inputs))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    results = [None] * len(jobs)
    save_results(args.output, results)
    print(f'Running {len(jobs)} jobs with {args.workers} worker(s). '
          'Concurrent jobs share CPU and memory; timings reflect this load.', flush=True)
    executor = ThreadPoolExecutor(max_workers=args.workers)
    futures = {}
    try:
        futures = {executor.submit(run_job, job, args): i for i, job in enumerate(jobs)}
        for completed, future in enumerate(as_completed(futures), 1):
            index = futures[future]
            results[index] = future.result()
            save_results(args.output, results)
            row = results[index][0]
            print(f"[{completed}/{len(jobs)}] {row['status']}: "
                  f"{row['file_name']} (path {row['path_flag']}) {row['message']}", flush=True)
    except KeyboardInterrupt:
        print(f'Interrupted. Saved results remain in {args.output}; '
              'waiting for running jobs to finish.', file=sys.stderr, flush=True)
        return 130
    finally:
        for future in futures:
            future.cancel()
        executor.shutdown(wait=True)
    failures = sum(result[0]['status'] == 'error' for result in results)
    print(f'Saved {args.output} and {metadata_path}; {failures} job(s) failed.')
    return 1 if failures else 0


if __name__ == '__main__':
    raise SystemExit(main())
