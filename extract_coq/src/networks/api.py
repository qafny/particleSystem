import json
import sys

import networks


def main() -> None:
    if len(sys.argv) < 2:
        raise ValueError(
            "usage: python3 api.py genmat_gate_cancellation <list_coef_json> <cnot_matrix_json> [singleq_matrix_json]"
        )

    name = sys.argv[1]
    if name == "genmat_gate_cancellation":
        if len(sys.argv) < 4:
            raise ValueError(
                "usage: python3 api.py genmat_gate_cancellation <list_coef_json> <cnot_matrix_json> [singleq_matrix_json]"
            )
        list_coef = json.loads(sys.argv[2])
        cnot_matrix = json.loads(sys.argv[3])
        singleq_matrix = json.loads(sys.argv[4]) if len(sys.argv) >= 5 else None
        mat = networks.genmat_gate_cancellation(list_coef, cnot_matrix, singleq_matrix)
        print(json.dumps(mat))
        return

    raise ValueError(f"unknown function: {name}")


if __name__ == "__main__":
    main()
