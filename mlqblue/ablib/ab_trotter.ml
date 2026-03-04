open QBlueSyntax

let scale_coeff (s : float) (((a, b), f) : lowprog_ten) : lowprog_ten = (((s *. a, s *. b), f) : lowprog_ten)

let flatten (xs : lowprog_ten list list) : lowprog =
  List.concat xs

let build_first_order ~(steps : int) ~(groups : lowprog_ten list list) : lowprog =
  let s = max 1 steps in
  let scale = 1.0 /. float_of_int s in
  let one_slice = List.map (fun g -> List.map (scale_coeff scale) g) groups |> flatten in
  let rec rep k acc = if k <= 0 then List.rev acc else rep (k - 1) (List.rev_append one_slice acc) in
  rep s []

let build_second_order ~(steps : int) ~(groups : lowprog_ten list list) : lowprog =
  let s = max 1 steps in
  let scale = 1.0 /. (2.0 *. float_of_int s) in
  let fwd = List.map (fun g -> List.map (scale_coeff scale) g) groups |> flatten in
  let bwd = List.map (fun g -> List.map (scale_coeff scale) g) (List.rev groups) |> flatten in
  let one_step = fwd @ bwd in
  let rec rep k acc = if k <= 0 then List.rev acc else rep (k - 1) (List.rev_append one_step acc) in
  rep s []

