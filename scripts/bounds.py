"""Second-order Trotter step counts: QBlue's bound vs OpenFermion's.

OpenFermion recommends r = trotter_steps_required_propagator(error_bound(terms), t, eps),
where error_bound (Poulin et al.) is the 1-norm of the second-order error
operator (tight) or a triangle-inequality estimate (loose). OpenFermion's own
error_bound is O(n^3) Python for the tight version, so it is recomputed here
with vectorized Pauli arithmetic; --check compares against OpenFermion on small
inputs. QBlue's r comes from results/qblue_results.csv (path_flag 2).
"""

import argparse
import csv
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

import numpy as np

from benchmark import ROOT, parse_hamiltonian

FIELDS = ["file_name", "error", "time", "nqubit", "nterms", "qblue_r2",
          "of_bound_tight", "of_bound_loose", "of_r2_tight", "of_r2_loose", "status", "message"]
MAX_TIGHT_TERMS = 3000
MAX_LOOSE_TERMS = 20000


def _pc(a):
    return np.bitwise_count(a).astype(np.int64)


def _encode(ph):
    """Binary symplectic form: bit k of x/z is qubit k (character k of the label)."""
    x = np.zeros(len(ph.paulis), dtype=np.uint64)
    z = np.zeros(len(ph.paulis), dtype=np.uint64)
    for i, label in enumerate(ph.paulis):
        for k, p in enumerate(label):
            if p in "XY":
                x[i] |= np.uint64(1 << k)
            if p in "ZY":
                z[i] |= np.uint64(1 << k)
    return x, z, np.array([c.real for c in ph.coeffs])


def _anticommute(x1, z1, x2, z2):
    return (_pc((x1 & z2) ^ (z1 & x2)) & 1).astype(bool)


def _product(x1, z1, e1, x2, z2):
    """(i^e1 P1) * P2 = i^e3 P3, with P = i^{x.z} X^x Z^z (so Y is the usual Y)."""
    x3, z3 = x1 ^ x2, z1 ^ z2
    e3 = (e1 + _pc(x1 & z1) + _pc(x2 & z2) + 2 * _pc(z1 & x2) - _pc(x3 & z3)) % 4
    return x3, z3, e3


def tight_bound(x, z, c, nq):
    """sum |coef| of OpenFermion's error_operator:
    1/12 sum_beta sum_{alpha<=beta} sum_{alpha'<beta} [H_alpha (1 - delta/2), [H_beta, H_alpha']]."""
    if 2 * nq > 62:
        raise ValueError("tight bound supports at most 31 qubits")
    phase = np.array([1, 1j, -1, -1j])
    keys_acc, vals_acc = [], []
    acc_keys, acc_vals = np.zeros(0, np.int64), np.zeros(0, complex)
    for b in range(len(c)):
        s = np.nonzero(_anticommute(x[b], z[b], x[:b], z[:b]))[0]
        if s.size == 0:
            continue
        # [P_b, P_a'] = 2 P_b P_a' for anticommuting pairs
        rx, rz, re = _product(x[b], z[b], 0, x[s], z[s])
        rc = 2 * c[b] * c[s]
        ax, az = x[:b + 1, None], z[:b + 1, None]
        mask = _anticommute(ax, az, rx[None, :], rz[None, :])
        ia, ir = np.nonzero(mask)
        if ia.size == 0:
            continue
        # [P_a, R] = 2 P_a R
        px, pz, pe = _product(x[ia], z[ia], 0, rx[ir], rz[ir])
        pe = (pe + re[ir]) % 4
        weight = np.where(ia == b, 0.5, 1.0)
        vals = 2 * c[ia] * weight * rc[ir] * phase[pe]
        keys = (px.astype(np.int64) << nq) | pz.astype(np.int64)
        keys_acc.append(keys)
        vals_acc.append(vals)
        if sum(k.size for k in keys_acc) > 5_000_000:
            acc_keys, acc_vals = _merge(acc_keys, acc_vals, keys_acc, vals_acc)
            keys_acc, vals_acc = [], []
    acc_keys, acc_vals = _merge(acc_keys, acc_vals, keys_acc, vals_acc)
    return float(np.abs(acc_vals).sum() / 12.0)


def _merge(acc_keys, acc_vals, keys_list, vals_list):
    keys = np.concatenate([acc_keys, *keys_list])
    vals = np.concatenate([acc_vals, *vals_list])
    uniq, inv = np.unique(keys, return_inverse=True)
    out = np.zeros(uniq.size, complex)
    np.add.at(out, inv, vals)
    return uniq, out


def loose_bound(x, z, c):
    """OpenFermion's tight=False estimate: sum_a 4|c_a| E_a (|c_a| + E_a),
    E_a = sum of |c_b| over b > a that do not commute with a."""
    total = 0.0
    ac = np.abs(c)
    for a in range(len(c)):
        anti = _anticommute(x[a], z[a], x[a + 1:], z[a + 1:])
        e = ac[a + 1:][anti].sum()
        total += 4.0 * ac[a] * e * (ac[a] + e)
    return float(total)


def openfermion_reference(ph):
    from openfermion import QubitOperator
    from openfermion.circuits.trotter.trotter_error import error_bound
    terms = [QubitOperator(" ".join(f"{p}{k}" for k, p in enumerate(label) if p != "I"), c.real)
             for label, c in zip(ph.paulis, ph.coeffs)]
    return error_bound(terms, tight=True), error_bound(terms, tight=False)


def job(reference, check):
    from openfermion.circuits.trotter.trotter_error import trotter_steps_required_propagator
    row = dict.fromkeys(FIELDS, "")
    for field in ("file_name", "error", "time", "nqubit"):
        row[field] = reference[field]
    row["qblue_r2"] = reference["trotter_step"]
    try:
        path = Path(reference["file_name"])
        if not path.is_absolute():
            path = ROOT / "mlqblue" / path
        ph = parse_hamiltonian(path)
        n = len(ph.paulis)
        row["nterms"] = n
        if n > MAX_LOOSE_TERMS:
            raise ValueError(f"more than {MAX_LOOSE_TERMS} terms")
        x, z, c = _encode(ph)
        t, eps = float(reference["time"]), float(reference["error"])
        loose = loose_bound(x, z, c)
        row.update(of_bound_loose=loose, of_r2_loose=trotter_steps_required_propagator(loose, t, eps))
        if n <= MAX_TIGHT_TERMS:
            tight = tight_bound(x, z, c, ph.n_qubits)
            row.update(of_bound_tight=tight, of_r2_tight=trotter_steps_required_propagator(tight, t, eps))
        if check and n <= 300:
            ref_tight, ref_loose = openfermion_reference(ph)
            if not (np.isclose(ref_tight, tight, rtol=1e-6) and np.isclose(ref_loose, loose, rtol=1e-6)):
                raise AssertionError(f"mismatch with OpenFermion: tight {tight} vs {ref_tight}, loose {loose} vs {ref_loose}")
        row["status"] = "ok"
    except Exception as error:
        row.update(status="error", message=str(error))
    return row


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=ROOT / "results/qblue_results.csv")
    parser.add_argument("--output", type=Path, default=ROOT / "results/bounds_results.csv")
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--check", action="store_true", help="compare with OpenFermion's error_bound (<= 300 terms)")
    args = parser.parse_args()
    with args.input.open(newline="") as source:
        references = [r for r in csv.DictReader(source) if r["path_flag"] == "2" and r["status"] == "ok"]
    with ProcessPoolExecutor(args.workers) as pool:
        rows = list(pool.map(job, references, [args.check] * len(references)))
    with args.output.open("w", newline="") as target:
        writer = csv.DictWriter(target, fieldnames=FIELDS)
        writer.writeheader()
        writer.writerows(rows)
    for row in rows:
        print(f"bounds: {row['file_name']}: {row['status']} {row['message']}", flush=True)
    return int(any(row["status"] != "ok" for row in rows))


if __name__ == "__main__":
    raise SystemExit(main())
