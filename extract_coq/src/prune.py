#!/usr/bin/env python3
from __future__ import annotations

import os
import re
import sys
import shutil
import subprocess
from dataclasses import dataclass
from collections import defaultdict, deque
from typing import Dict, Set, List, Iterable


@dataclass(frozen=True)
class Config:
    gen_dir: str
    out_dir: str            
    roots: List[str]         # module names without .ml
    keep: Set[str]           # extra modules to keep (if they exist)
    verbose: bool = True


def die(msg: str, code: int = 2) -> None:
    print(f"[prune] ERROR: {msg}", file=sys.stderr)
    raise SystemExit(code)


def ensure_dir_exists(path: str) -> None:
    if not os.path.isdir(path):
        die(f"Directory not found: {path}")


def list_ml_modules(gen_dir: str) -> Set[str]:
    ensure_dir_exists(gen_dir)
    return {f[:-3] for f in os.listdir(gen_dir) if f.endswith(".ml")}


def run_ocamldep_modules(gen_dir: str, ml_files: List[str]) -> str:
    cmd = ["ocamldep", "-modules"] + ml_files
    try:
        return subprocess.check_output(cmd, text=True, cwd=gen_dir)
    except FileNotFoundError:
        die("ocamldep not found. Ensure your opam switch is active and ocamldep is in PATH.")
    except subprocess.CalledProcessError as e:
        die(f"ocamldep failed: {e}")


def parse_ocamldep_output(ocamldep_out: str, have: Set[str]) -> Dict[str, Set[str]]:
    """
    ocamldep -modules output lines look like:
      Foo.ml: Bar Baz
    We keep only dependencies that exist as modules in `have`.
    """
    deps: Dict[str, Set[str]] = defaultdict(set)
    pat = re.compile(r"^(.+?)\s*:\s*(.*)$")

    for line in ocamldep_out.splitlines():
        line = line.strip()
        if not line:
            continue
        m = pat.match(line)
        if not m:
            continue

        file_part = os.path.basename(m.group(1).strip())
        mod = file_part[:-3] if file_part.endswith(".ml") else file_part
        rhs = m.group(2).strip()

        if rhs:
            for d in rhs.split():
                if d in have:
                    deps[mod].add(d)

        deps.setdefault(mod, set())

    return deps


def compute_reachable(roots: Iterable[str], deps: Dict[str, Set[str]], have: Set[str]) -> Set[str]:
    need: Set[str] = set()
    q = deque()

    for r in roots:
        if r not in have:
            die(f"Root module '{r}' not found in gen_dir (expected '{r}.ml').")
        q.append(r)

    while q:
        u = q.popleft()
        if u in need:
            continue
        need.add(u)
        for v in deps.get(u, ()):
            if v not in need:
                q.append(v)

    return need


def recreate_dir(path: str) -> None:
    if os.path.exists(path):
        shutil.rmtree(path)
    os.makedirs(path, exist_ok=True)


def copy_modules(gen_dir: str, out_dir: str, modules: Iterable[str]) -> List[str]:
    copied: List[str] = []
    for m in sorted(modules):
        ml_src = os.path.join(gen_dir, f"{m}.ml")

        if not os.path.exists(ml_src):
            continue

        shutil.copy2(ml_src, os.path.join(out_dir, f"{m}.ml"))
        copied.append(m)

    return copied


def prune(cfg: Config) -> List[str]:
    have = list_ml_modules(cfg.gen_dir)
    ml_files = sorted([f"{m}.ml" for m in have])

    ocamldep_out = run_ocamldep_modules(cfg.gen_dir, ml_files)
    deps = parse_ocamldep_output(ocamldep_out, have)

    reachable = compute_reachable(cfg.roots, deps, have)

    extras = {m for m in cfg.keep if m in have}
    needed = reachable | extras

    recreate_dir(cfg.out_dir)
    copied = copy_modules(cfg.gen_dir, cfg.out_dir, needed)

    if cfg.verbose:
        print(f"[prune] gen_dir = {cfg.gen_dir}")
        print(f"[prune] out_dir = {cfg.out_dir}")
        print(f"[prune] roots  = {', '.join(cfg.roots)}")
        if extras:
            print(f"[prune] keep   = {', '.join(sorted(extras))}")
        print(f"[prune] kept {len(copied)} modules:")
        for m in copied:
            print(f"  - {m}")

    return copied


def parse_args(argv: List[str]) -> Config:
    """
    Usage:
      prune.py <gen_dir> <out_dir> <Root1> [<Root2> ...] [--keep=ModA,ModB] [--quiet]
    """
    if len(argv) < 4:
        die("Usage: prune.py <gen_dir> <out_dir> <Root1> [<Root2> ...] [--keep=ModA,ModB] [--quiet]")

    gen_dir = argv[1]
    out_dir = argv[2]

    roots: List[str] = []
    keep: Set[str] = set()
    verbose = True

    i = 3
    while i < len(argv) and not argv[i].startswith("--"):
        roots.append(argv[i])
        i += 1

    while i < len(argv):
        a = argv[i]
        if a == "--quiet":
            verbose = False
        elif a.startswith("--keep="):
            val = a.split("=", 1)[1].strip()
            if val:
                keep |= {x.strip() for x in val.split(",") if x.strip()}
        else:
            die(f"Unknown argument: {a}")
        i += 1

    if not roots:
        die("You must provide at least one root module name (without .ml).")

    return Config(gen_dir=gen_dir, out_dir=out_dir, roots=roots, keep=keep, verbose=verbose)


def main() -> None:
    cfg = parse_args(sys.argv)
    prune(cfg)


if __name__ == "__main__":
    main()
