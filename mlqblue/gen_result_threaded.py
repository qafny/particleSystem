"""Run CSV jobs concurrently, using one independent OCaml process per job."""

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import csv
import os
from pathlib import Path
import tempfile

import gen_result


def positive_int(value):
    value = int(value)
    if value < 1:
        raise argparse.ArgumentTypeError("workers must be at least 1")
    return value


def parse_args():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("-i", "--input", required=True, help="Input job CSV.")
    parser.add_argument("-o", "--output", default="result_qblue_threaded.csv")
    parser.add_argument("-e", "--error", type=float, default=0.1)
    parser.add_argument("-t", "--time", dest="time_value", type=float, default=0.7854)
    parser.add_argument("-p", "--path-flag", type=int, default=0)
    parser.add_argument("--allow-job-errors", action="store_true",
                        help="Exit successfully after saving results even if individual jobs failed.")
    parser.add_argument("-w", "--workers", type=positive_int, default=1,
                        help="Concurrent OCaml processes (default: 1).")
    return parser.parse_args()


def run_job(job):
    file_name, error, time_value, path_flag = job
    row = dict.fromkeys(gen_result.CSV_FIELDS, "")
    row.update(file_name=file_name, error=error, time=time_value, path_flag=path_flag)
    try:
        result = gen_result.call_ocaml(*job)
        for field in gen_result.CSV_FIELDS:
            if field in result:
                row[field] = result[field]
        row["time"] = result.get("time", result.get("simu_time", time_value))
        row.update(status="ok", message="")
    except Exception as exc:
        row.update(status="error", message=str(exc))
    return row


def save_results(output, rows):
    """Atomically save completed rows in input order after each completion."""
    output = Path(output)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w", newline="", encoding="utf-8", dir=output.parent,
            prefix=f".{output.name}.", suffix=".tmp", delete=False,
        ) as handle:
            temporary = Path(handle.name)
            writer = csv.DictWriter(handle, fieldnames=gen_result.CSV_FIELDS)
            writer.writeheader()
            writer.writerows(row for row in rows if row is not None)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, output)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def run_jobs(jobs, output, workers):
    rows = [None] * len(jobs)
    save_results(output, rows)
    executor = ThreadPoolExecutor(max_workers=workers)
    futures = {}
    try:
        futures = {executor.submit(run_job, job): i for i, job in enumerate(jobs)}
        for completed, future in enumerate(as_completed(futures), 1):
            index = futures[future]
            rows[index] = future.result()
            save_results(output, rows)
            row = rows[index]
            print(f"[{completed}/{len(jobs)}] {row['status']}: "
                  f"{row['file_name']} (path {row['path_flag']})", flush=True)
    finally:
        for future in futures:
            future.cancel()
        # Running subprocesses finish normally; queued jobs are cancelled.
        executor.shutdown(wait=True)
    return rows


def main():
    args = parse_args()
    if Path(args.input).resolve() == Path(args.output).resolve():
        raise SystemExit("Input and output CSV paths must be different.")
    jobs = gen_result.parse_input_file(
        args.input, args.error, args.time_value, args.path_flag,
    )
    gen_result.get_performance_executable()
    missing = sorted({job[0] for job in jobs if not Path(job[0]).is_file()})
    if missing:
        raise SystemExit("Missing input files (run from mlqblue):\n" + "\n".join(missing))
    print(f"Running {len(jobs)} jobs with {args.workers} worker(s). "
          "Concurrent jobs share CPU and memory; compilation timings reflect this load.",
          flush=True)
    try:
        rows = run_jobs(jobs, args.output, args.workers)
    except KeyboardInterrupt:
        raise SystemExit("Interrupted. Previously saved results remain in " + args.output)
    failures = sum(row["status"] == "error" for row in rows)
    print(f"Saved to {args.output}; {failures} job(s) failed.")
    return int(failures > 0 and not args.allow_job_errors)


if __name__ == "__main__":
    raise SystemExit(main())
