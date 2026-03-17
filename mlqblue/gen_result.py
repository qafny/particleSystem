import subprocess
import json
import csv
import argparse
from pathlib import Path


CSV_FIELDS = [
    "file_name",
    "error",
    "time",
    "path_flag",
    "nqubit",
    "program_size",
    "compilation_time",
    "compilation_terms",
    "single_qubit_gates",
    "multi_qubit_gates",
    "single_qubit_gates_bfopt",
    "multi_qubit_gates_bfopt",
    "trotter_step",
    "status",
    "message",
]

REPO_ROOT = Path(__file__).resolve().parent
PERFORMANCE_EXE = REPO_ROOT / "_build" / "default" / "performance.exe"


def get_performance_executable():
    if not PERFORMANCE_EXE.is_file():
        raise FileNotFoundError(
            f"Expected built executable at {PERFORMANCE_EXE}. "
            "Build it first, for example with `dune build performance.exe`."
        )

    return PERFORMANCE_EXE


def call_ocaml(file_name, error, time_value, path_flag):
    proc = subprocess.run(
        [
            str(get_performance_executable()),
            file_name,
            "-e",
            str(error),
            "-t",
            str(time_value),
            "-p",
            str(path_flag),
        ],
        text=True,
        capture_output=True,
        check=False
    )

    if proc.returncode != 0:
        raise RuntimeError(proc.stderr.strip())

    return json.loads(proc.stdout)


def parse_input_file(input_path, default_error, default_time, default_path_flag):
    rows = []
    with open(input_path, "r", newline="", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        required = {"file_name"}
        if not reader.fieldnames or not required.issubset(set(reader.fieldnames)):
            raise ValueError(
                "Input CSV must include at least the 'file_name' column. "
                "Optional columns: error,time,path_flag"
            )

        for item in reader:
            file_name = (item.get("file_name") or "").strip()
            if not file_name:
                continue
            error = float(item["error"]) if item.get("error") not in (None, "") else default_error
            time_value = float(item["time"]) if item.get("time") not in (None, "") else default_time
            path_flag = int(item["path_flag"]) if item.get("path_flag") not in (None, "") else default_path_flag
            rows.append((file_name, error, time_value, path_flag))

    return rows


def parse_args():
    parser = argparse.ArgumentParser(
        description="Run performance.exe over a list of inputs and save CSV results."
    )
    parser.add_argument(
        "-i", "--input",
        default=None,
        help="Input CSV file with columns: file_name,error,time,path_flag (error/time/path_flag optional)."
    )
    parser.add_argument(
        "-o", "--output",
        default="result_qblue.csv",
        help="Output CSV file path. Default: result_qblue.csv"
    )
    parser.add_argument(
        "-e", "--error",
        type=float,
        default=0.1,
        help="Default error value when not provided in input CSV. Default: 0.1"
    )
    parser.add_argument(
        "-t", "--time",
        dest="time_value",
        type=float,
        default=0.7854,
        help="Default time value when not provided in input CSV. Default: 0.7854"
    )
    parser.add_argument(
        "-p", "--path-flag",
        type=int,
        default=0,
        help="Default path_flag when not provided in input CSV. Default: 0"
    )
    return parser.parse_args()


def main():
    args = parse_args()

    # One example argument set for performance.exe
    default_arg_list = [
		("DataSet1/small/MarqSim_Ar.txt", 0.1, 0.7854, 1),
		]

    if args.input:
        input_path = Path(args.input)
        arg_list = parse_input_file(
            input_path,
            default_error=args.error,
            default_time=args.time_value,
            default_path_flag=args.path_flag
        )
    else:
        arg_list = default_arg_list

    rows = []

    print('file, error, time, path_flag')
    for file_name, error, time_value, path_flag in arg_list:
        try:
            print(file_name, error, time_value, path_flag)
            result = call_ocaml(file_name, error, time_value, path_flag)

            row = {
                "file_name": result.get("file_name"),
                "error": result.get("error"),
                "time": result.get("time", result.get("simu_time")),
                "path_flag": result.get("path_flag"),
				"nqubit": result.get("nqubit"),
				"program_size": result.get("program_size"),
                "compilation_time": result.get("compilation_time"),
                "compilation_terms": result.get("compilation_terms"),
                "single_qubit_gates": result.get("single_qubit_gates"),
                "multi_qubit_gates": result.get("multi_qubit_gates"),
                "single_qubit_gates_bfopt": result.get("single_qubit_gates_bfopt"),
                "multi_qubit_gates_bfopt": result.get("multi_qubit_gates_bfopt"),
                "trotter_step": result.get("trotter_step"),
                "status": "ok",
                "message": ""
            }

        except Exception as e:
            row = {
                "file_name": file_name,
                "error": error,
                "time": time_value,
                "path_flag": path_flag,
                "nqubit": "",
                "program_size": "",
                "compilation_time": "",
                "compilation_terms": "",
                "single_qubit_gates": "",
                "multi_qubit_gates": "",
                "single_qubit_gates_bfopt": "",
                "multi_qubit_gates_bfopt": "",
                "trotter_step": "",
                "status": "error",
                "message": str(e)
            }

        rows.append(row)
        print(row)

    with open(args.output, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(
            f,
            fieldnames=CSV_FIELDS
        )
        writer.writeheader()
        writer.writerows(rows)

    print(f"Saved to {args.output}")


if __name__ == "__main__":
    main()
