import subprocess
import json
import csv

def call_ocaml(file_name, error, time_value, path_flag):
    proc = subprocess.run(
        [
            "dune",
            "exec",
            "--",
            "./performance.exe",
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


def main():
    # One example argument set for performance.exe
    arg_list = [
        ("DataSet1/large/BK_benzene_sto3g_42_electrons_72_spin_orbitals_Hamiltonian_368021_paulis.txt", 0.1, 0.7854, 3),
		# ("DataSet1/small/MarqSim_Ar.txt", 0.1, 0.7854, 0),
		("DataSet1/small/MarqSim_Ar.txt", 0.1, 0.7854, 1),
		# ("DataSet1/small/MarqSim_Ar.txt", 0.1, 0.7854, 2),
		# ("DataSet1/small/MarqSim_Ar.txt", 0.1, 0.7854, 3),
		# ("DataSet1/small/MarqSim_Ar.txt", 0.1, 0.7854, 4),
		# ("DataSet1/small/MarqSim_BeH2_f.txt", 0.1, 0.7854, 0),
		# ("DataSet1/small/MarqSim_BeH2_f.txt", 0.1, 0.7854, 1),
		# ("DataSet1/small/MarqSim_BeH2_f.txt", 0.1, 0.7854, 2),
		# ("DataSet1/small/MarqSim_BeH2_f.txt", 0.1, 0.7854, 3),
		# ("DataSet1/small/MarqSim_BeH2_f.txt", 0.1, 0.7854, 4),
		# ("DataSet1/small/MarqSim_BeH2_unf.txt", 0.1, 0.7854, 0),
		# ("DataSet1/small/MarqSim_BeH2_unf.txt", 0.1, 0.7854, 1),
		# ("DataSet1/small/MarqSim_BeH2_unf.txt", 0.1, 0.7854, 2),
		# ("DataSet1/small/MarqSim_BeH2_unf.txt", 0.1, 0.7854, 3),
		# ("DataSet1/small/MarqSim_BeH2_unf.txt", 0.1, 0.7854, 4),
		# # ("DataSet1/small/MarqSim_Cl-.txt", 0.1, 0.7854, 0),
		# ("DataSet1/small/MarqSim_Cl-.txt", 0.1, 0.7854, 1),
		# ("DataSet1/small/MarqSim_Cl-.txt", 0.1, 0.7854, 2),
		# ("DataSet1/small/MarqSim_Cl-.txt", 0.1, 0.7854, 3),
		# ("DataSet1/small/MarqSim_Cl-.txt", 0.1, 0.7854, 4),
		# # ("DataSet1/small/MarqSim_H2O.txt", 0.1, 0.7854, 0),
		# ("DataSet1/small/MarqSim_H2O.txt", 0.1, 0.7854, 1),
		# ("DataSet1/small/MarqSim_H2O.txt", 0.1, 0.7854, 2),
		# ("DataSet1/small/MarqSim_H2O.txt", 0.1, 0.7854, 3),
		# ("DataSet1/small/MarqSim_H2O.txt", 0.1, 0.7854, 4),
		# # ("DataSet1/small/MarqSim_HF.txt", 0.1, 0.7854, 0),
		# ("DataSet1/small/MarqSim_HF.txt", 0.1, 0.7854, 1),
		# ("DataSet1/small/MarqSim_HF.txt", 0.1, 0.7854, 2),
		# ("DataSet1/small/MarqSim_HF.txt", 0.1, 0.7854, 3),
		# ("DataSet1/small/MarqSim_HF.txt", 0.1, 0.7854, 4),
		# ("DataSet1/small/MarqSim_LiH_f.txt", 0.1, 0.7854, 0),
		# ("DataSet1/small/MarqSim_LiH_f.txt", 0.1, 0.7854, 1),
		# ("DataSet1/small/MarqSim_LiH_f.txt", 0.1, 0.7854, 2),
		# ("DataSet1/small/MarqSim_LiH_f.txt", 0.1, 0.7854, 3),
		# ("DataSet1/small/MarqSim_LiH_f.txt", 0.1, 0.7854, 4),
		# ("DataSet1/small/MarqSim_LiH_unf.txt", 0.1, 0.7854, 0),
		# ("DataSet1/small/MarqSim_LiH_unf.txt", 0.1, 0.7854, 1),
		# ("DataSet1/small/MarqSim_LiH_unf.txt", 0.1, 0.7854, 2),
		# ("DataSet1/small/MarqSim_LiH_unf.txt", 0.1, 0.7854, 3),
		# ("DataSet1/small/MarqSim_LiH_unf.txt", 0.1, 0.7854, 4),
		# ("DataSet1/small/MarqSim_Na+.txt", 0.1, 0.7854, 0),
		# ("DataSet1/small/MarqSim_Na+.txt", 0.1, 0.7854, 1),
		# ("DataSet1/small/MarqSim_Na+.txt", 0.1, 0.7854, 2),
		# ("DataSet1/small/MarqSim_Na+.txt", 0.1, 0.7854, 3),
		# ("DataSet1/small/MarqSim_Na+.txt", 0.1, 0.7854, 4),
		# ("DataSet1/small/MarqSim_OH-.txt", 0.1, 0.7854, 0),
		# ("DataSet1/small/MarqSim_OH-.txt", 0.1, 0.7854, 1),
		# ("DataSet1/small/MarqSim_OH-.txt", 0.1, 0.7854, 2),
		# ("DataSet1/small/MarqSim_OH-.txt", 0.1, 0.7854, 3),
		# ("DataSet1/small/MarqSim_OH-.txt", 0.1, 0.7854, 4),
		# ("DataSet1/small/MarqSim_SYK1.txt", 0.1, 0.7854, 0),
		# ("DataSet1/small/MarqSim_SYK1.txt", 0.1, 0.7854, 1),
		# ("DataSet1/small/MarqSim_SYK1.txt", 0.1, 0.7854, 2),
		# ("DataSet1/small/MarqSim_SYK1.txt", 0.1, 0.7854, 3),
		# ("DataSet1/small/MarqSim_SYK1.txt", 0.1, 0.7854, 4),
		# ("DataSet1/small/MarqSim_SYK2.txt", 0.1, 0.7854, 0),
		("DataSet1/small/MarqSim_SYK2.txt", 0.1, 0.7854, 1),
		# ("DataSet1/small/MarqSim_SYK2.txt", 0.1, 0.7854, 2),
		# ("DataSet1/small/MarqSim_SYK2.txt", 0.1, 0.7854, 3),
		# ("DataSet1/small/MarqSim_SYK2.txt", 0.1, 0.7854, 4),
	]

    rows = []

    print('file, error, time, path_flag')
    for file_name, error, time_value, path_flag in arg_list:
        try:
            print(file_name, error, time_value, path_flag)
            result = call_ocaml(file_name, error, time_value, path_flag)

            row = {
                "file_name": result.get("file_name"),
                "error": result.get("error"),
                "time": result.get("time"),
                "path_flag": result.get("path_flag"),
				"nqubit": result.get("nqubit"),
				"npau": result.get("npau"),
                "single_qubit_gates": result.get("single_qubit_gates"),
                "multi_qubit_gates": result.get("multi_qubit_gates"),
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
                "npau": "",
                "single_qubit_gates": "",
                "multi_qubit_gates": "",
                "status": "error",
                "message": str(e)
            }

        rows.append(row)

    with open("result_qblue.csv", "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(
            f,
            fieldnames=[
                "file_name", "error", "time", "path_flag",
                "nqubit", "npau",
   				"single_qubit_gates", "multi_qubit_gates",
                "status", "message"
            ]
        )
        writer.writeheader()
        writer.writerows(rows)

    print("Saved to result_qblue.csv")


if __name__ == "__main__":
    main()
