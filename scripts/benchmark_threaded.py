"""Run OpenFermion and Phoenix concurrently with independent Python processes."""

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import csv
import os
from pathlib import Path
import subprocess
import sys
import tempfile

from benchmark import ROOT

COMPILERS = ("openfermion", "phoenix")
SCRIPTS = Path(__file__).resolve().parent


def positive_int(value):
    value = int(value)
    if value < 1:
        raise argparse.ArgumentTypeError("workers must be at least 1")
    return value


def save_results(path, fields, rows):
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w", newline="", encoding="utf-8", dir=path.parent,
            prefix=f".{path.name}.", suffix=".tmp", delete=False,
        ) as target:
            temporary = Path(target.name)
            writer = csv.DictWriter(target, fieldnames=fields)
            writer.writeheader()
            writer.writerows(row for row in rows if row is not None)
            target.flush()
            os.fsync(target.fileno())
        os.replace(temporary, path)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def run_job(compiler, fields, references):
    try:
        with tempfile.TemporaryDirectory(prefix=f"qblue-{compiler}-") as directory:
            source = Path(directory) / "input.csv"
            output = Path(directory) / "output.csv"
            save_results(source, fields, references)
            process = subprocess.run(
                [sys.executable, str(SCRIPTS / f"{compiler}_bench.py"),
                 "--input", str(source), "--output", str(output)],
                capture_output=True, text=True,
            )
            if output.exists():
                with output.open(newline="") as handle:
                    reader = csv.DictReader(handle)
                    rows = list(reader)
                    if reader.fieldnames == fields and len(rows) == len(references):
                        if process.returncode in (0, 1):
                            return rows
            raise RuntimeError(process.stderr.strip() or "Compiler did not produce the expected CSV rows")
    except Exception as error:
        rows = []
        for reference in references:
            row = dict.fromkeys(fields, "")
            for field in ("file_name", "error", "time", "path_flag", "nqubit", "program_size", "trotter_step"):
                row[field] = reference[field]
            row.update(status="error", message=str(error))
            rows.append(row)
        return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--allow-job-errors", action="store_true",
                        help="Exit successfully after saving results even if individual jobs failed.")
    parser.add_argument("--input", type=Path, default=ROOT / "results/qblue_results.csv")
    parser.add_argument("--output-dir", type=Path, default=ROOT / "results")
    parser.add_argument("--workers", type=positive_int, default=1,
                        help="Concurrent compiler processes (default: 1)")
    parser.add_argument("--compiler", choices=COMPILERS,
                        help="Run only this compiler (default: both)")
    args = parser.parse_args()
    compilers = (args.compiler,) if args.compiler else COMPILERS
    outputs = {name: args.output_dir / f"{name}_results.csv" for name in compilers}
    if args.input.resolve() in {path.resolve() for path in outputs.values()}:
        parser.error("Input and output must differ")
    with args.input.open(newline="") as source:
        reader = csv.DictReader(source)
        fields = reader.fieldnames
        required = {"file_name", "error", "time", "path_flag", "nqubit", "program_size", "trotter_step", "status", "message"}
        if not fields or not required.issubset(fields):
            parser.error("Expected a qblue_result.csv schema")
        references = [row for row in reader if int(row["path_flag"]) == 1]
    groups = {}
    for index, row in enumerate(references):
        path = Path(row["file_name"])
        if not path.is_absolute():
            path = ROOT / "mlqblue" / path
        groups.setdefault((path.resolve(), float(row["time"])), []).append(index)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    results = {name: [None] * len(references) for name in compilers}
    for name, path in outputs.items():
        save_results(path, fields, results[name])
    print(f"Running {len(groups) * len(compilers)} jobs with {args.workers} worker(s). "
          "Compilation timings reflect concurrent CPU and memory load.", flush=True)
    executor = ThreadPoolExecutor(max_workers=args.workers)
    futures = {}
    try:
        for name in compilers:
            for indices in groups.values():
                future = executor.submit(run_job, name, fields, [references[i] for i in indices])
                futures[future] = name, indices
        for completed, future in enumerate(as_completed(futures), 1):
            name, indices = futures[future]
            rows = future.result()
            for index, row in zip(indices, rows):
                results[name][index] = row
            save_results(outputs[name], fields, results[name])
            failures = sum(row["status"] == "error" for row in rows)
            print(f"[{completed}/{len(futures)}] {name}: {rows[0]['file_name']} "
                  f"({failures} failed rows)", flush=True)
    except KeyboardInterrupt:
        raise SystemExit("Interrupted; completed results remain saved")
    finally:
        for future in futures:
            future.cancel()
        executor.shutdown(wait=True)
    failures = sum(row["status"] == "error" for rows in results.values() for row in rows)
    print(f"Saved results to {args.output_dir}; {failures} row(s) failed")
    return int(failures > 0 and not args.allow_job_errors)


if __name__ == "__main__":
    raise SystemExit(main())
