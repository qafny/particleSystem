(* File: common.ml *)


type paulimat =
| Coq_paulix
| Coq_pauliy
| Coq_pauliz
| Coq_paulii

type lowprog_ten = (float * float) * (int -> paulimat)

type lowprog = lowprog_ten list

let rec list_to_map_aux l n = 
   match l with [] -> (fun _ -> Coq_paulii)
              | x::xs -> (fun i -> if i = n then x else list_to_map_aux xs (n+1) i)
let list_to_map l = list_to_map_aux l 0
