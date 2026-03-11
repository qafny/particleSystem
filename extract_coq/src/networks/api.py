import json
import sys

import networks


def _read_json_arg(raw: str):
    if raw.startswith("@"):
        with open(raw[1:], "r", encoding="utf-8") as f:
            raw = f.read()
    return json.loads(raw)


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
        list_coef = _read_json_arg(sys.argv[2])
        cnot_matrix = _read_json_arg(sys.argv[3])
        singleq_matrix = _read_json_arg(sys.argv[4]) if len(sys.argv) >= 5 else None
        mat = networks.genmat_gate_cancellation(list_coef, cnot_matrix, singleq_matrix)
        print(json.dumps(mat))
        return

    raise ValueError(f"unknown function: {name}")


if __name__ == "__main__":
    main()
