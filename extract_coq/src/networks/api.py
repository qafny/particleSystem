import hashlib
import json
import os
import sys
import tempfile

try:
    import fcntl
except ImportError:  # not available on Windows
    fcntl = None

import networks


def _raw_arg(raw: str) -> str:
    if raw.startswith("@"):
        with open(raw[1:], "r", encoding="utf-8") as f:
            return f.read()
    return raw


def _read_json_arg(raw: str):
    return json.loads(_raw_arg(raw))


def _cached(args, compute):
    """The transition matrix depends only on the Hamiltonian, not on the error
    or time, so cache it when QBLUE_MARQSIM_CACHE names a directory."""
    cache_dir = os.environ.get("QBLUE_MARQSIM_CACHE")
    if not cache_dir:
        return compute()
    key = hashlib.sha256("\0".join(_raw_arg(a) for a in args).encode()).hexdigest()
    path = os.path.join(cache_dir, key + ".json")
    os.makedirs(cache_dir, exist_ok=True)
    # one process computes a given matrix; concurrent jobs for the same
    # Hamiltonian wait for it instead of each building the flow network
    with open(path + ".lock", "w") as lock:
        if fcntl is not None:
            fcntl.flock(lock, fcntl.LOCK_EX)
        if os.path.exists(path):
            with open(path, encoding="utf-8") as f:
                return json.load(f)
        result = compute()
        with tempfile.NamedTemporaryFile("w", dir=cache_dir, delete=False, suffix=".tmp") as f:
            json.dump(result, f)
        os.replace(f.name, path)
    return result


def main() -> None:
    if len(sys.argv) < 2:
        raise ValueError(
            "usage: python3 api.py genmat_gate_cancellation <list_coef_json> <cnot_matrix_json> [singleq_matrix_json]"
        )

    name = sys.argv[1]
    if name == "genmat_gate_cancellation":
        if len(sys.argv) < 4:
            raise ValueError(
                "usage: python3.9 api.py genmat_gate_cancellation <list_coef_json> <cnot_matrix_json> [singleq_matrix_json]"
            )
        def compute():
            list_coef = _read_json_arg(sys.argv[2])
            cnot_matrix = _read_json_arg(sys.argv[3])
            singleq_matrix = _read_json_arg(sys.argv[4]) if len(sys.argv) >= 5 else None
            return networks.genmat_gate_cancellation(list_coef, cnot_matrix, singleq_matrix)

        mat = _cached(sys.argv[2:], compute)
        print(json.dumps(mat))
        return

    # phase angles for the QSP-based LCU methods; they depend only on the
    # polynomial, so they share the cache (keyed with the function name)
    if name == "qsvt_phases":
        import qsp_phases
        print(json.dumps(_cached(sys.argv[1:], lambda: qsp_phases.qsvt_phases(
            _read_json_arg(sys.argv[2]), int(_read_json_arg(sys.argv[3]))))))
        return
    if name == "gqsp_complement":
        import qsp_phases
        print(json.dumps(_cached(sys.argv[1:], lambda: qsp_phases.gqsp_complement(
            _read_json_arg(sys.argv[2]), _read_json_arg(sys.argv[3])))))
        return

    raise ValueError(f"unknown function: {name}")


if __name__ == "__main__":
    main()
