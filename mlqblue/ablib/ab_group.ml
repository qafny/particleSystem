open QBlueSyntax

module XZ = struct
  type t = { x : Z.t; z : Z.t }

  let anticomm a b =
    let v = Z.logxor (Z.logand a.x b.z) (Z.logand a.z b.x) in
    (Z.popcount v mod 2) = 1

  let not_qwc a b =
    let both = Z.logand (Z.logor a.x a.z) (Z.logor b.x b.z) in
    let mismatch = Z.logor (Z.logxor a.x b.x) (Z.logxor a.z b.z) in
    not (Z.equal (Z.logand both mismatch) Z.zero)
end

let term_to_xz (nq : int) ((_, f) : lowprog_ten) : XZ.t =
  let x = ref Z.zero in
  let z = ref Z.zero in
  for i = 0 to nq - 1 do
    let bit = Z.shift_left Z.one i in
    match f i with
    | Coq_paulii -> ()
    | Coq_paulix -> x := Z.logor !x bit
    | Coq_pauliz -> z := Z.logor !z bit
    | Coq_pauliy ->
        x := Z.logor !x bit;
        z := Z.logor !z bit
  done;
  { XZ.x = !x; z = !z }

let greedy_coloring (edge : XZ.t -> XZ.t -> bool) (xs : XZ.t array) : int array =
  let m = Array.length xs in
  let deg = Array.make m 0 in
  for i = 0 to m - 1 do
    let d = ref 0 in
    for j = 0 to m - 1 do
      if i <> j && edge xs.(i) xs.(j) then incr d
    done;
    deg.(i) <- !d
  done;
  let order = Array.init m (fun i -> i) in
  Array.sort (fun i j -> compare deg.(j) deg.(i)) order;
  let colors = Array.make m (-1) in
  let rec pick_color used k =
    if List.mem k used then pick_color used (k + 1) else k
  in
  Array.iter
    (fun v ->
      let used = ref [] in
      for u = 0 to m - 1 do
        if u <> v && colors.(u) <> -1 && edge xs.(v) xs.(u) then used := colors.(u) :: !used
      done;
      colors.(v) <- pick_color !used 0)
    order;
  colors

let bucket_by_color (colors : int array) (terms : lowprog_ten array) : lowprog_ten list list =
  let cmax = Array.fold_left max (-1) colors in
  let buckets = Array.init (cmax + 1) (fun _ -> []) in
  Array.iteri (fun i c -> buckets.(c) <- terms.(i) :: buckets.(c)) colors;
  Array.to_list (Array.map List.rev buckets)

type invariant_ = FC | QWC

let group (inv : invariant_) (nq : int) (lp : lowprog) : lowprog_ten list list =
  let terms = Array.of_list lp in
  let xzs = Array.map (term_to_xz nq) terms in
  let edge =
    match inv with
    | FC -> XZ.anticomm
    | QWC -> XZ.not_qwc
  in
  let colors = greedy_coloring edge xzs in
  bucket_by_color colors terms

let group_fc = group FC
let group_qwc = group QWC
