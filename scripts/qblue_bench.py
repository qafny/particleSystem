#!/usr/bin/env python3
"""
Run QBlue (mlqblue/performance.exe) over benchmark datasets and write a CSV.

Focuses on TODO.md items:
- per-benchmark compilation time (wall clock)
- resource estimates (qubits + gate counts)
- sweeps over (err, t) and pipeline choices

It also detects dataset format differences:
- MarQSim_dataset: "+ <float> * <IXYZ...>"
- Genesis_dataset: "<IXYZ...> (<float>+0j)"
Genesis inputs are converted on-the-fly using scripts/genesis_to_marqsim.py.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Optional


ROOT = Path(__file__).resolve().parents[1]
MLQBLUE = ROOT / "mlqblue"
PERF_EXE = MLQBLUE / "_build" / "default" / "performance.exe"
GENESIS_CONVERTER = ROOT / "scripts" / "genesis_to_marqsim.py"


_MARQSIM_LINE_RE = re.compile(r"^\s*[+-]\s+(?:\d+(?:\.\d*)?)(?:[eE][-+]?\d+)?\s*\*\s*[IXYZ]+\s*$")
_GENESIS_LINE_RE = re.compile(r"^\s*[IXYZ]+\s+\(\s*[-+]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][-+]?\d+)?\s*\+\s*0j\s*\)\s*$")

_INPUT_RE = re.compile(r"Input circuit uses\s+(\d+)\s+qubits,\s+has\s+(\d+)\s+gates:\s+\{([^}]*)\}")
_AFTER_RE = re.compile(r"After optimization, the circuit uses\s+(\d+)\s+gates\s+:\s+\{([^}]*)\}")

_ALGO_HEADER_RE = re.compile(r"----\s*(.*?)\s*->\s*(.*?)\s*circuits:\s*----")
_NTERMS_RE = re.compile(r"Length of Pauli String\s+(\d+)")
_DEALING_STD_RE = re.compile(
    r"Dealing with\s+(\d+)\s+pauli strings;\s+relaxation factor:\s+([-+]?[\d.]+(?:[eE][-+]?\d+)?);\s+splitting r:\s+(\d+)\."
)
_DEALING_QDRIFT_RE = re.compile(
    r"Dealing with\s+(\d+)\s+pauli strings;\s+lambda\s*=\s*([-+]?[\d.]+(?:[eE][-+]?\d+)?);\s+relaxation factor:\s+([-+]?[\d.]+(?:[eE][-+]?\d+)?)\."
)


def _parse_kv_list(braced: str) -> dict[str, int]:
    # Example: " H : 0, X : 0, Rzq : 3, CX : 0 "
    out: dict[str, int] = {}
    for chunk in braced.split(","):
        chunk = chunk.strip()
        if not chunk:
            continue
        if ":" not in chunk:
            continue
        k, v = chunk.split(":", 1)
        out[k.strip()] = int(v.strip())
    return out


def detect_format(path: Path) -> str:
    # Return "marqsim" | "genesis" | "unknown"
    with path.open("r", encoding="utf-8", errors="replace") as f:
        for _ in range(50):
            line = f.readline()
            if not line:
                break
            s = line.strip()
            if not s:
                continue
            if _MARQSIM_LINE_RE.match(s):
                return "marqsim"
            if _GENESIS_LINE_RE.match(s):
                return "genesis"
    return "unknown"


def iter_input_files(dataset: str) -> list[Path]:
    base = ROOT / "QBlue_Benchmark_Datasets"
    if dataset == "marqsim":
        files = list((base / "MarQSim_dataset").glob("*.txt"))
        # Prefer smaller instances first (useful when compute time is limited).
        return sorted(files, key=lambda p: (p.stat().st_size, str(p)))
    if dataset == "genesis":
        files = list((base / "Genesis_dataset").rglob("*.txt"))
        # Prefer smaller instances first (useful for smoke tests).
        return sorted(files, key=lambda p: (p.stat().st_size, str(p)))
    if dataset == "all":
        mar = list((base / "MarQSim_dataset").glob("*.txt"))
        mar = sorted(mar, key=lambda p: (p.stat().st_size, str(p)))
        gen = list((base / "Genesis_dataset").rglob("*.txt"))
        gen = sorted(gen, key=lambda p: (p.stat().st_size, str(p)))
        return mar + gen
    raise ValueError(f"unknown dataset: {dataset}")


@dataclass(frozen=True)
class RunResult:
    ok: bool
    wall_s: float
    algorithm: str = ""
    backend: str = ""
    n_terms: Optional[int] = None
    n_pauli_strings: Optional[int] = None
    splitting_r: Optional[int] = None
    lambda_val: Optional[float] = None
    relaxation_factor: Optional[float] = None
    qubits: Optional[int] = None
    gates_in_total: Optional[int] = None
    gates_in: Optional[dict[str, int]] = None
    gates_opt_total: Optional[int] = None
    gates_opt: Optional[dict[str, int]] = None
    stdout_tail: str = ""
    stderr_tail: str = ""


def _ensure_text(s: object) -> str:
    if s is None:
        return ""
    if isinstance(s, bytes):
        return s.decode("utf-8", errors="replace")
    return str(s)


def _parse_metrics(combined: str) -> dict[str, object]:
    algo = None
    backend = None
    n_terms = None
    n_pauli_strings = None
    splitting_r = None
    lambda_ = None
    relaxation_factor = None

    qubits = None
    gates_in_total = None
    gates_in = None
    gates_opt_total = None
    gates_opt = None

    for line in combined.splitlines():
        # Note: most of performance.exe's debug output uses stderr, and may be
        # prefixed by "[DBG] ". Keep regexes permissive and just search.
        m = _ALGO_HEADER_RE.search(line)
        if m:
            algo = m.group(1).strip()
            backend = m.group(2).strip()

        m = _NTERMS_RE.search(line)
        if m:
            n_terms = int(m.group(1))

        m = _DEALING_STD_RE.search(line)
        if m:
            n_pauli_strings = int(m.group(1))
            relaxation_factor = float(m.group(2))
            splitting_r = int(m.group(3))

        m = _DEALING_QDRIFT_RE.search(line)
        if m:
            n_pauli_strings = int(m.group(1))
            lambda_ = float(m.group(2))
            relaxation_factor = float(m.group(3))

        m = _INPUT_RE.search(line)
        if m:
            qubits = int(m.group(1))
            gates_in_total = int(m.group(2))
            gates_in = _parse_kv_list(m.group(3))

        m = _AFTER_RE.search(line)
        if m:
            gates_opt_total = int(m.group(1))
            gates_opt = _parse_kv_list(m.group(2))

    return {
        "algorithm": algo,
        "backend": backend,
        "n_terms": n_terms,
        "n_pauli_strings": n_pauli_strings,
        "splitting_r": splitting_r,
        "lambda": lambda_,
        "relaxation_factor": relaxation_factor,
        "qubits": qubits,
        "gates_in_total": gates_in_total,
        "gates_in": gates_in,
        "gates_opt_total": gates_opt_total,
        "gates_opt": gates_opt,
    }


def run_one(
    perf_exe: Path,
    mlqblue_dir: Path,
    input_file: Path,
    err: float,
    t: float,
    p: int,
    grouping: str,
    timeout_s: int,
) -> RunResult:
    cmd = [
        "opam",
        "exec",
        "--",
        str(perf_exe),
        str(input_file),
        "-e",
        str(err),
        "-t",
        str(t),
        "-p",
        str(p),
        "-g",
        grouping,
    ]
    t0 = time.time()
    try:
        proc = subprocess.run(
            cmd,
            cwd=str(mlqblue_dir),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=timeout_s,
            check=False,
        )
        wall = time.time() - t0
    except subprocess.TimeoutExpired as e:
        wall = time.time() - t0
        out = _ensure_text(getattr(e, "stdout", ""))
        errout = _ensure_text(getattr(e, "stderr", ""))
        combined = out + ("\n" if out and errout else "") + errout
        metrics = _parse_metrics(combined)
        return RunResult(
            ok=False,
            wall_s=wall,
            algorithm=str(metrics.get("algorithm") or ""),
            backend=str(metrics.get("backend") or ""),
            n_terms=metrics["n_terms"] if isinstance(metrics["n_terms"], int) else None,
            n_pauli_strings=metrics["n_pauli_strings"] if isinstance(metrics["n_pauli_strings"], int) else None,
            splitting_r=metrics["splitting_r"] if isinstance(metrics["splitting_r"], int) else None,
            lambda_val=metrics["lambda"] if isinstance(metrics["lambda"], float) else None,
            relaxation_factor=metrics["relaxation_factor"] if isinstance(metrics["relaxation_factor"], float) else None,
            qubits=metrics["qubits"] if isinstance(metrics["qubits"], int) else None,
            gates_in_total=metrics["gates_in_total"] if isinstance(metrics["gates_in_total"], int) else None,
            gates_in=metrics["gates_in"] if isinstance(metrics["gates_in"], dict) else None,
            gates_opt_total=metrics["gates_opt_total"] if isinstance(metrics["gates_opt_total"], int) else None,
            gates_opt=metrics["gates_opt"] if isinstance(metrics["gates_opt"], dict) else None,
            stdout_tail=(out[-4000:] if out else errout[-4000:]),
            stderr_tail=errout[-4000:],
        )

    out = _ensure_text(proc.stdout)
    errout = _ensure_text(proc.stderr)
    combined = out + ("\n" if out and errout else "") + errout
    metrics = _parse_metrics(combined)
    qubits = metrics["qubits"] if isinstance(metrics["qubits"], int) else None
    gates_in_total = metrics["gates_in_total"] if isinstance(metrics["gates_in_total"], int) else None
    gates_in = metrics["gates_in"] if isinstance(metrics["gates_in"], dict) else None
    gates_opt_total = metrics["gates_opt_total"] if isinstance(metrics["gates_opt_total"], int) else None
    gates_opt = metrics["gates_opt"] if isinstance(metrics["gates_opt"], dict) else None

    ok = proc.returncode == 0 and qubits is not None and gates_opt_total is not None
    return RunResult(
        ok=ok,
        wall_s=wall,
        algorithm=str(metrics.get("algorithm") or ""),
        backend=str(metrics.get("backend") or ""),
        n_terms=metrics["n_terms"] if isinstance(metrics["n_terms"], int) else None,
        n_pauli_strings=metrics["n_pauli_strings"] if isinstance(metrics["n_pauli_strings"], int) else None,
        splitting_r=metrics["splitting_r"] if isinstance(metrics["splitting_r"], int) else None,
        lambda_val=metrics["lambda"] if isinstance(metrics["lambda"], float) else None,
        relaxation_factor=metrics["relaxation_factor"] if isinstance(metrics["relaxation_factor"], float) else None,
        qubits=qubits,
        gates_in_total=gates_in_total,
        gates_in=gates_in,
        gates_opt_total=gates_opt_total,
        gates_opt=gates_opt,
        # performance.exe's "dbg" output is typically on stderr. To avoid writing
        # an always-empty column, prefer stdout, but fall back to stderr.
        stdout_tail=(out[-4000:] if out else errout[-4000:]),
        stderr_tail=errout[-4000:],
    )


def ensure_built() -> None:
    if PERF_EXE.exists():
        return
    qblue_syntax = MLQBLUE / "qbluelib" / "QBlueSyntax.ml"
    if not qblue_syntax.exists():
        raise FileNotFoundError(
            f"Missing extracted Coq output: {qblue_syntax}\n"
            f"Fix:\n"
            f"  1) cd {ROOT / 'extract_coq'} && bash extract.sh\n"
            f"  2) cp {ROOT / 'extract_coq' / 'ml'}/*.ml {qblue_syntax.parent}/\n"
            f"  3) cd {MLQBLUE} && opam exec -- dune build"
        )
    subprocess.check_call(["opam", "exec", "--", "dune", "build"], cwd=str(MLQBLUE))


def convert_genesis_to_tmp(genesis_file: Path, tmp_dir: Path) -> Path:
    tmp_out = tmp_dir / (genesis_file.name + ".marqsim.txt")
    subprocess.check_call(
        [sys.executable, str(GENESIS_CONVERTER), str(genesis_file), "-o", str(tmp_out)],
        cwd=str(ROOT),
    )
    return tmp_out


def normalize_newlines_to_tmp(input_file: Path, tmp_dir: Path) -> Path:
    """
    Write a normalized copy of input_file to tmp_dir with Unix newlines.

    This avoids modifying datasets in-place while working around tools that
    treat literal '\\r' characters as lexer errors.
    """
    bs = input_file.read_bytes()
    if b"\r" not in bs:
        return input_file

    # Convert CRLF and bare CR to LF.
    norm = bs.replace(b"\r\n", b"\n").replace(b"\r", b"\n")
    h = hashlib.sha1(str(input_file).encode("utf-8")).hexdigest()[:12]
    tmp_out = tmp_dir / f"{input_file.stem}.{h}.unix{input_file.suffix}"
    tmp_out.write_bytes(norm)
    return tmp_out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dataset", choices=["marqsim", "genesis", "all"], default="marqsim")
    ap.add_argument(
        "--inputs",
        nargs="+",
        type=Path,
        default=None,
        help="Explicit list of input files (overrides --dataset). Relative paths are resolved against CWD then repo root.",
    )
    ap.add_argument("--out", type=Path, default=Path("qblue_results.csv"))
    ap.add_argument(
        "--perf-exe",
        type=Path,
        default=PERF_EXE,
        help="Path to mlqblue performance.exe (default: mlqblue/_build/default/performance.exe)",
    )
    ap.add_argument("--mlqblue-dir", type=Path, default=MLQBLUE, help="Path to mlqblue directory (default: ./mlqblue)")
    ap.add_argument("--errs", nargs="+", type=float, default=[1e-1, 1e-3])
    ap.add_argument("--ts", nargs="+", type=float, default=[0.1, 0.5, 1.0])
    ap.add_argument(
        "--pipelines",
        nargs="+",
        choices=["auto", "std", "qdrift", "ab1", "ab2"],
        default=["auto", "std", "qdrift"],
        help="Pipeline selector; maps to performance.exe -p flag.",
    )
    ap.add_argument(
        "--grouping",
        choices=["none", "qwc", "fc"],
        default="none",
        help="Grouping mode passed to performance.exe -g (ab1/ab2 only; std/qdrift currently ignore it).",
    )
    ap.add_argument("--timeout-s", type=int, default=1800)
    ap.add_argument("--limit", type=int, default=0, help="Limit number of input files (0 = no limit)")
    ap.add_argument("--no-build", action="store_true", help="Do not run dune build if performance.exe is missing")
    args = ap.parse_args()

    def resolve_path(p: Path, *, base: Path) -> Path:
        if p.is_absolute():
            return p
        if p.exists():
            return p.resolve()
        alt = (base / p)
        if alt.exists():
            return alt.resolve()
        return p

    # Resolve mlqblue dir and perf exe for robustness in batch environments.
    args.mlqblue_dir = resolve_path(args.mlqblue_dir, base=ROOT)
    args.perf_exe = resolve_path(args.perf_exe, base=args.mlqblue_dir)
    if not args.perf_exe.exists():
        args.perf_exe = resolve_path(args.perf_exe, base=ROOT)

    if not args.no_build and args.perf_exe == PERF_EXE:
        try:
            ensure_built()
        except FileNotFoundError as e:
            print(f"ERROR: {e}", file=sys.stderr)
            return 2
        except subprocess.CalledProcessError as e:
            print(f"ERROR: dune build failed (exit {e.returncode}).", file=sys.stderr)
            return int(e.returncode) if e.returncode else 2
    if not args.perf_exe.exists():
        print(
            f"ERROR: Missing {args.perf_exe}. Build with: (cd {args.mlqblue_dir} && opam exec -- dune build)",
            file=sys.stderr,
        )
        return 2

    input_files = [resolve_path(p, base=ROOT) for p in args.inputs] if args.inputs else iter_input_files(args.dataset)
    if args.limit and args.limit > 0:
        input_files = input_files[: args.limit]

    # Preflight format check.
    counts: dict[str, int] = {"marqsim": 0, "genesis": 0, "unknown": 0}
    for f in input_files:
        counts[detect_format(f)] += 1
    print(f"Detected formats: {counts}", file=sys.stderr)

    # performance.exe uses `-p <int>` as a path/algorithm selector:
    #   0 => std trotterization (Coq)
    #   1 => qdrift (Coq)
    #   2 => ablib first-order trotter
    #   3 => ablib second-order (Strang)
    # Keep "auto" for backward compatibility (it maps to qdrift).
    pipeline_to_p = {"auto": 1, "std": 0, "qdrift": 1, "ab1": 2, "ab2": 3}

    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("w", newline="", encoding="utf-8") as csvf:
        w = csv.DictWriter(
            csvf,
            fieldnames=[
                "dataset",
                "format",
                "input_path",
                "input_name",
                "err",
                "t",
                "pipeline",
                "p_flag",
                "grouping",
                "algorithm",
                "backend",
                "n_terms",
                "n_pauli_strings",
                "splitting_r",
                "lambda",
                "relaxation_factor",
                "ok",
                "wall_s",
                "qubits",
                "gates_in_total",
                "gates_in_H",
                "gates_in_X",
                "gates_in_Rzq",
                "gates_in_CX",
                "gates_in_json",
                "gates_opt_total",
                "gates_opt_U1",
                "gates_opt_U2",
                "gates_opt_U3",
                "gates_opt_CX",
                "gates_opt_json",
                "stdout_tail",
                "stderr_tail",
            ],
        )
        w.writeheader()

        with tempfile.TemporaryDirectory(prefix="qblue_bench_") as td:
            tmp_dir = Path(td)
            for input_file in input_files:
                fmt = detect_format(input_file)
                if "MarQSim_dataset" in str(input_file):
                    dataset = "MarQSim_dataset"
                elif "Genesis_dataset" in str(input_file):
                    dataset = "Genesis_dataset"
                else:
                    dataset = "custom"

                run_file = input_file
                if fmt == "genesis":
                    try:
                        run_file = convert_genesis_to_tmp(input_file, tmp_dir)
                    except subprocess.CalledProcessError as e:
                        w.writerow(
                            {
                                "dataset": dataset,
                                "format": fmt,
                                "input_path": str(input_file),
                                "input_name": input_file.name,
                                "err": "",
                                "t": "",
                                "pipeline": "",
                                "ok": False,
                                "wall_s": 0.0,
                                "qubits": "",
                                "gates_in_total": "",
                                "gates_in_H": "",
                                "gates_in_X": "",
                                "gates_in_Rzq": "",
                                "gates_in_CX": "",
                                "gates_opt_total": "",
                                "gates_opt_U1": "",
                                "gates_opt_U2": "",
                                "gates_opt_U3": "",
                                "gates_opt_CX": "",
                                "stdout_tail": "",
                                "stderr_tail": f"genesis conversion failed: {e}",
                            }
                        )
                        continue
                else:
                    # MarQSim (and some "unknown") files may be CRLF-encoded; normalize to
                    # avoid OCaml lexer errors on literal '\r'.
                    run_file = normalize_newlines_to_tmp(run_file, tmp_dir)

                for err in args.errs:
                    for t in args.ts:
                        for pipeline in args.pipelines:
                            p = pipeline_to_p[pipeline]
                            rr = run_one(
                                args.perf_exe,
                                args.mlqblue_dir,
                                run_file,
                                err,
                                t,
                                p,
                                args.grouping,
                                args.timeout_s,
                            )
                            gates_in = rr.gates_in or {}
                            gates_opt = rr.gates_opt or {}
                            w.writerow(
                                {
                                    "dataset": dataset,
                                    "format": fmt,
                                    "input_path": str(input_file),
                                    "input_name": input_file.name,
                                    "err": err,
                                    "t": t,
                                    "pipeline": pipeline,
                                    "p_flag": p,
                                    "grouping": args.grouping,
                                    "algorithm": rr.algorithm,
                                    "backend": rr.backend,
                                    "n_terms": rr.n_terms if rr.n_terms is not None else "",
                                    "n_pauli_strings": rr.n_pauli_strings if rr.n_pauli_strings is not None else "",
                                    "splitting_r": rr.splitting_r if rr.splitting_r is not None else "",
                                    "lambda": rr.lambda_val if rr.lambda_val is not None else "",
                                    "relaxation_factor": rr.relaxation_factor if rr.relaxation_factor is not None else "",
                                    "ok": rr.ok,
                                    "wall_s": f"{rr.wall_s:.6f}",
                                    "qubits": rr.qubits if rr.qubits is not None else "",
                                    "gates_in_total": rr.gates_in_total if rr.gates_in_total is not None else "",
                                    "gates_in_H": gates_in.get("H", ""),
                                    "gates_in_X": gates_in.get("X", ""),
                                    "gates_in_Rzq": gates_in.get("Rzq", ""),
                                    "gates_in_CX": gates_in.get("CX", ""),
                                    "gates_in_json": json.dumps(gates_in, sort_keys=True) if gates_in else "",
                                    "gates_opt_total": rr.gates_opt_total if rr.gates_opt_total is not None else "",
                                    "gates_opt_U1": gates_opt.get("U1", ""),
                                    "gates_opt_U2": gates_opt.get("U2", ""),
                                    "gates_opt_U3": gates_opt.get("U3", ""),
                                    "gates_opt_CX": gates_opt.get("CX", ""),
                                    "gates_opt_json": json.dumps(gates_opt, sort_keys=True) if gates_opt else "",
                                    "stdout_tail": rr.stdout_tail.replace("\n", "\\n"),
                                    "stderr_tail": rr.stderr_tail.replace("\n", "\\n"),
                                }
                            )
                            csvf.flush()
                            if rr.ok:
                                try:
                                    os.fsync(csvf.fileno())
                                except OSError:
                                    # Some filesystems / streams may not support fsync.
                                    pass
                            if not rr.ok:
                                print(
                                    f"WARN: failed {input_file.name} err={err} t={t} pipeline={pipeline} (see CSV tails)",
                                    file=sys.stderr,
                                )
                            else:
                                print(
                                    f"OK: {input_file.name} err={err} t={t} pipeline={pipeline} wall_s={rr.wall_s:.2f}",
                                    file=sys.stderr,
                                )

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
