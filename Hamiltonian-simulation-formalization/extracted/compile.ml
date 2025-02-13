let rec read_file_aux chan =
    try
        let c = input_char chan in
            c :: (read_file_aux chan)
    with End_of_file -> [];;

let rec write_to_file chan lst =
    match lst with
    | head :: tail ->
            output_char chan head;
            write_to_file chan tail
    | [] -> ()

let compile in_filename out_filename numSlices =
    let in_file = open_in in_filename in
    let in_program_body = read_file_aux in_file in
    let compilation_result = Compile_coq.compile in_program_body numSlices in
    let out_file = open_out out_filename in
    write_to_file out_file compilation_result;;

let s = Sys.argv.(3);;

match Array.length Sys.argv with
| 4 -> compile Sys.argv.(1) Sys.argv.(2) (List.init (String.length s) (String.get s))
| _ -> Printf.printf "usage: ./compile program.ham program.qasm 1000\n"
;;
