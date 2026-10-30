From SQIR Require Import ExtractionGateSet.

From QBlue Require Import QBlueUtility.
From QBlue Require Import QBlueCompile.
From QBlue Require Import QBlueSynthDigital.
From QBlue Require Import QBlueQuantumWalk.
From QBlue Require Import QBlueQubitization.
From QBlue Require Import QBlueQSVT.
From QBlue Require Import QBlueQSVT_updateQSP.
From QBlue Require Import QBlueTTS_v4.
From QBlue Require Import QBlueQSVT_updateQSP.

Require Coq.extraction.Extraction.
(* Standard utilities for bools, options, etc. *)
Require Coq.extraction.ExtrOcamlBasic.

(* A few common functions not included in ExtrOcamlBasic. *)
Extract Inlined Constant fst => "fst".
Extract Inlined Constant snd => "snd".
Extract Inlined Constant negb => "not".

(* Most List functions have the same mapping, no need to define 
 open the following if the mapping is needed *)
(* Blacklist make extraction produce List0 rather than List, which can shadow Stdlib.List funcs *)
Extraction Blacklist List.
Require Import List.
Extract Inlined Constant List.fold_left => "(fun f l acc -> Stdlib.List.fold_left f acc l)".
Extract Inlined Constant List.fold_right => "(fun f acc l -> Stdlib.List.fold_right f l acc)".
Extract Inlined Constant List.nth_error => "Stdlib.List.nth_opt".
Extract Inlined Constant List.hd_error => "(fun l -> Stdlib.List.nth_opt l 0)".
Extract Inlined Constant List.length => "Stdlib.List.length".
Extract Inlined Constant List.app => "Stdlib.List.append".
Extract Inlined Constant List.map => "Stdlib.List.map".
Extract Inlined Constant List.rev => "Stdlib.List.rev".
Extract Inlined Constant List.rev_append => "Stdlib.List.rev_append".
Extract Inlined Constant List.forallb => "Stdlib.List.for_all".
Extract Inlined Constant List.existsb => "Stdlib.List.exists".
Extract Inlined Constant List.filter => "Stdlib.List.filter".
Extract Inlined Constant List.tl => "Stdlib.List.tl".

(* Standard extraction from nat -> OCaml int and Z -> OCaml int. *)
Require Export QArith.
Require Coq.extraction.ExtrOcamlNatInt.
Require Coq.extraction.ExtrOcamlZInt.

(* Inline a few operations. *)
Extraction Inline plus mult Nat.eq_dec.
Extraction Inline Z.add Z.sub Z.mul.

(* Otherwise sub will be extracted to the (undefined) string "sub". *)
Extract Inlined Constant Init.Nat.sub => "(-)".
Extract Inlined Constant INR => "Float.of_int".
Extract Inlined Constant IZR => "Float.of_int".


(* Custom extraction from R -> OCaml float. *)
Require Export Reals Reals.ROrderedType.
Extract Inlined Constant R => "float".
Extract Inlined Constant R0 => "0.0".
Extract Inlined Constant R1 => "1.0".
Extract Inlined Constant R2 => "2.0".
Extract Inlined Constant Rplus => "( +. )".
Extract Inlined Constant Rmult => "( *. )".
Extract Inlined Constant Ropp => "((-.) 0.0)".
Extract Inlined Constant Rinv => "((/.) 1.0)".
Extract Inlined Constant Rminus => "( -. )".
Extract Inlined Constant Rdiv => "( /. )".
Extract Inlined Constant sqrt => "sqrt".
Extract Inlined Constant Rabs => "abs_float".
Extract Inlined Constant pow => "(fun a b -> a ** (float_of_int b))".
Extract Inlined Constant ln => "log".
Extract Inlined Constant cos => "cos".
Extract Inlined Constant sin => "sin".
Extract Inlined Constant tan => "tan".
Extract Inlined Constant atan => "atan".
Extract Inlined Constant acos => "acos".
Extract Inlined Constant asin => "asin".
Extract Inlined Constant exp => "Float.exp".

(* Bessel J_k(tau): Miller backward recurrence, normalised to J_0+2*J_2+...=1 *)
Extract Constant QBlue.QBlueQuantumWalk.bessel_j =>
  "(fun k tau ->
    let tau = abs_float tau in
    if tau < 1e-15 then (if k = 0 then 1.0 else 0.0)
    else begin
      (* m robust bound: k + tau + offset based on log(1/eps) *)
      let m = max k (int_of_float tau) + 40 in
      let b = Array.make (m + 2) 0.0 in
      b.(m) <- 1e-30;
      for i = m - 1 downto 0 do
        b.(i) <- 2.0 *. float_of_int (i+1) /. tau *. b.(i+1) -. b.(i+2);
        if b.(i) > 1e100 then (for j = i to m do b.(j) <- b.(j) *. 1e-100 done)
      done;
      let sum = ref b.(0) in
      let i = ref 2 in
      while !i <= m do sum := !sum +. 2.0 *. b.(!i); i := !i + 2 done;
      if k <= m then b.(k) /. !sum else 0.0
    end)".

Extract Constant QBlue.QBlueQuantumWalk.findK_qwalk =>
  "(fun tau eps ->
    let tau = abs_float tau in
    let eps = max eps 1e-18 in
    let k_try = int_of_float (tau *. 2.0 +. 40.0 +. log (1.0 /. eps) *. 2.0) in
    let b = Array.make (k_try + 2) 0.0 in
    b.(k_try) <- 1e-30;
    for i = k_try - 1 downto 0 do
      b.(i) <- 2.0 *. float_of_int (i+1) /. tau *. b.(i+1) -. b.(i+2);
      if b.(i) > 1e100 then (for j = i to k_try do b.(j) <- b.(j) *. 1e-100 done)
    done;
    let sum = ref b.(0) in
    let i = ref 2 in
    while !i <= k_try do sum := !sum +. 2.0 *. b.(!i); i := !i + 2 done;
    let norm_b k = if k <= k_try then b.(k) /. !sum else 0.0 in
    let tail = ref 0.0 in
    let best = ref k_try in
    for k = k_try downto 1 do
      tail := !tail +. 2.0 *. abs_float (norm_b k);
      if !tail < eps then best := k - 1
    done;
    !best)".

Extract Inlined Constant PI => "Float.pi".
Extract Inlined Constant QBlueUtility.Reqb => "Stdlib.( = )".
Extract Inlined Constant ChangeRotationBasis.Rltb => "Stdlib.( < )".
Extract Inlined Constant QBlueUtility.Rltb => "Stdlib.( < )".
Extract Inlined Constant Coq.Reals.ROrderedType.Reqb => "Stdlib.( = )".
Extract Inlined Constant Rlt_dec => "( < )".
Extract Inlined Constant Rle_dec => "( <= )".
Extract Inlined Constant Req_dec => "( = )".

(* ================================================================== *)
(*  Solver 1: Haah 2019                                               *)
(*  Product decomposition via FFT + 2x2 matrix iteration.             *)
(*  Based on Julia notebook implementation (X.M., 02/2020).           *)
(*                                                                     *)
(*  Steps:                                                            *)
(*   1. Build Jacobi-Anger even coefficients for cos(tau*x)/2         *)
(*      a[m] = (-1)^m * J_{2m}(tau)/2  for m = 0,...,d               *)
(*   2. Evaluate A on D = next_pow2(2*(d+1)) roots of unity           *)
(*      A(e^{i*theta_j}) = a[0] + 2*sum_{m>=1} a[m]*cos(2m*theta_j) *)
(*   3. Compute C_j = sqrt(1 - A_j^2) (simplified; avoids root find) *)
(*   4. FFT [A_j] -> C11 coefficients; FFT [i*C_j] -> C12 coefficients*)
(*   5. Build d+1 matrix polynomial entries at even Laurent degrees    *)
(*   6. Matrix iteration: extract d+1 phases phi[0]..phi[d]           *)
(*      - tmp_P = C_end^dag * C_end; P_i = tmp_P/tr(tmp_P)           *)
(*      - phi[d+1-i] = getarg(P_i[0,1])                              *)
(*      - C_new[j] = C[j]*Q_i + C[j+1]*P_i                          *)
(*      - phi[0] = getarg(C_final[0,0])                              *)
(* ================================================================== *)
 
Extract Constant QBlue.QBlueQSVT_updateQSP.haah_qsp_solver =>
"(fun d tau err ->
  let pi = Float.pi in
  let bj k t = QBlueQuantumWalk.bessel_j k t in
  let deg_n = d in
 
  (* Step 1: Jacobi-Anger even Laurent coefficients, scaled by 0.5 *)
  let a_pos = Array.init (deg_n + 1) (fun m ->
    if m = 0 then bj 0 tau *. 0.5
    else let sign = if m mod 2 = 0 then 1.0 else -1.0 in
         sign *. bj (2*m) tau *. 0.5) in
 
  (* Step 2: FFT grid size D = next power of 2 >= 2*(deg_n+1) *)
  let d_fft =
    let n = ref 1 in
    while !n < 2*(deg_n+1) do n := !n * 2 done; !n in
 
  (* Evaluate A(e^{i*theta_j}) = a[0] + 2*sum a[m]*cos(2m*theta_j) *)
  let a_vals = Array.init d_fft (fun j ->
    let theta = 2.0 *. pi *. float_of_int j /. float_of_int d_fft in
    let s = ref a_pos.(0) in
    for m = 1 to deg_n do
      s := !s +. 2.0 *. a_pos.(m) *. cos(2.0 *. float_of_int m *. theta)
    done; !s) in
 
  (* Step 3: C_j = sqrt(1 - A_j^2) [real, avoids root finding] *)
  let c_vals = Array.map (fun a ->
    let v = 1.0 -. a *. a in
    if v < 0.0 then 0.0 else sqrt v) a_vals in
 
  (* Step 4: Cooley-Tukey FFT in-place *)
  let fft_ip re im n =
    let bits = ref 0 in
    let tmp = ref 1 in
    while !tmp < n do tmp := !tmp * 2; incr bits done;
    for i = 0 to n-1 do
      let j = ref 0 in
      for b = 0 to !bits-1 do
        if (i lsr b) land 1 = 1 then j := !j lor (1 lsl (!bits-1-b))
      done;
      if !j > i then begin
        let t = re.(i) in re.(i) <- re.(!j); re.(!j) <- t;
        let t = im.(i) in im.(i) <- im.(!j); im.(!j) <- t
      end
    done;
    let len = ref 2 in
    while !len <= n do
      let ang = -2.0 *. pi /. float_of_int !len in
      let wr = cos ang and wi = sin ang in
      let k = ref 0 in
      while !k < n do
        let cr = ref 1.0 and ci = ref 0.0 in
        for j = 0 to !len/2 - 1 do
          let ur = re.(!k+j) and ui = im.(!k+j) in
          let vr = !cr *. re.(!k+j+!len/2) -. !ci *. im.(!k+j+!len/2) in
          let vi = !cr *. im.(!k+j+!len/2) +. !ci *. re.(!k+j+!len/2) in
          re.(!k+j) <- ur +. vr; im.(!k+j) <- ui +. vi;
          re.(!k+j+!len/2) <- ur -. vr; im.(!k+j+!len/2) <- ui -. vi;
          let nr = !cr *. wr -. !ci *. wi in
          ci := !cr *. wi +. !ci *. wr; cr := nr
        done; k := !k + !len
      done; len := !len * 2
    done in
 
  (* FFT of A (real) -> C11 *)
  let c11r = Array.copy a_vals and c11i = Array.make d_fft 0.0 in
  fft_ip c11r c11i d_fft;
  (* FFT of i*C (purely imaginary) -> C12 *)
  let c12r = Array.make d_fft 0.0 and c12i = Array.copy c_vals in
  fft_ip c12r c12i d_fft;
 
  let inv_d = 1.0 /. float_of_int d_fft in
  let gc11 k = let i = if k>=0 then k else d_fft+k in
               (c11r.(i)*.inv_d, c11i.(i)*.inv_d) in
  let gc12 k = let i = if k>=0 then k else d_fft+k in
               (c12r.(i)*.inv_d, c12i.(i)*.inv_d) in
 
  (* Step 5: Build deg_n+1 matrix polynomial at even Laurent degrees *)
  let cms = Array.init (deg_n+1) (fun m ->
    let k = 2*(m - deg_n) in
    let c11 = gc11 k in let c12 = gc12 k in
    let c21 = (-. fst c12, -. snd c12) in
    [|[|c11;c12|];[|c21;c11|]|]) in
 
  (* Step 6: Matrix operations and phase extraction *)
  let cadd (a,b)(c,d) = (a+.c,b+.d) in
  let cmul (a,b)(c,d) = (a*.c-.b*.d, a*.d+.b*.c) in
  let cdiv (a,b)(c,d) = let s=c*.c+.d*.d in
    ((a*.c+.b*.d)/.s,(b*.c-.a*.d)/.s) in
  let cconj (a,b) = (a,-.b) in
  let mm a b =
    [|[|cadd(cmul a.(0).(0) b.(0).(0))(cmul a.(0).(1) b.(1).(0));
        cadd(cmul a.(0).(0) b.(0).(1))(cmul a.(0).(1) b.(1).(1))|];
      [|cadd(cmul a.(1).(0) b.(0).(0))(cmul a.(1).(1) b.(1).(0));
        cadd(cmul a.(1).(0) b.(0).(1))(cmul a.(1).(1) b.(1).(1))|]|] in
  let mct a =
    [|[|cconj a.(0).(0);cconj a.(1).(0)|];
      [|cconj a.(0).(1);cconj a.(1).(1)|]|] in
  let mtr a = cadd a.(0).(0) a.(1).(1) in
  let msc s m = Array.map (Array.map (fun x -> cdiv x s)) m in
  let getarg (a,b) =
    let nm = sqrt(a*.a+.b*.b) in if nm < 1e-15 then 0.0
    else let an=a/.nm and bn=b/.nm in
         let xr = acos(max(-1.0)(min 1.0 an)) in
         let xi = asin(max(-1.0)(min 1.0 bn)) in
         if xi > 0.0 then (if xr > 0.0 then xr-.2.0*.pi else xr)
         else -.xr in
  let phis = Array.make (deg_n+1) 0.0 in
  let ca = Array.init (deg_n+1) (fun i ->
    Array.init 2 (fun r -> Array.init 2 (fun c -> cms.(i).(r).(c)))) in
  let sz = ref (deg_n+1) in
  for i = 1 to deg_n do
    let s = !sz in
    let tp = mm (mct ca.(s-1)) ca.(s-1) in
    let tq = mm (mct ca.(0))   ca.(0) in
    let pi_ = msc (mtr tp) tp in
    let qi  = msc (mtr tq) tq in
    phis.(deg_n+1-i) <- getarg pi_.(0).(1);
    for j = 0 to s-2 do
      ca.(j) <- Array.init 2 (fun r -> Array.init 2 (fun c ->
        cadd (mm ca.(j) qi).(r).(c) (mm ca.(j+1) pi_).(r).(c)))
    done; sz := s-1
  done;
  phis.(0) <- getarg ca.(0).(0).(0);
  Array.to_list phis)".
 
 
(* ================================================================== *)
(*  Solver 2: Dong, Meng, Whaley, Lin 2021                           *)
(*  Optimization-based (L-BFGS) phase-factor evaluation.              *)
(*  Works in standard float64; stable for any tau and degree d.       *)
(*                                                                     *)
(*  Steps:                                                            *)
(*   1. Chebyshev nodes x_k = cos(pi*(2k+1)/(2*(d+1))) k=0..d        *)
(*   2. Target f(x_k) = cos(tau*x_k)/2                               *)
(*   3. QSP unitary U(Φ,x) = R(phi_0)*W(x)*R(phi_1)*...*R(phi_d)    *)
(*      where W(x)=[[x, i*s],[i*s,x]] s=sqrt(1-x^2), R(p)=e^{i*p*Z}*)
(*   4. Gradient ∂L/∂phi_j via forward-backward matrix product pass  *)
(*   5. L-BFGS with m=10 history vectors and Wolfe line search        *)
(* ================================================================== *)
 
Extract Constant QBlue.QBlueQSVT_updateQSP.donglin_qsp_solver =>
"(fun d tau err ->
  let pi = Float.pi in
  let n = d + 1 in
 
  (* Chebyshev nodes on [-1,1] *)
  let xs = Array.init n (fun k ->
    cos(pi *. (2.0 *. float_of_int k +. 1.0) /. (2.0 *. float_of_int n))) in
 
  (* Target: cos(tau*x)/2 at each node *)
  let ft = Array.map (fun x -> cos(tau *. x) *. 0.5) xs in
 
  (* Complex arithmetic: (float*float) matching C extraction *)
  let cadd (a,b)(c,d) = (a+.c, b+.d) in
  let cmul (a,b)(c,d) = (a*.c-.b*.d, a*.d+.b*.c) in
 
  (* Signal unitary W(x) = [[x, i*s],[i*s, x]] where s=sqrt(1-x^2) *)
  let w_mat x =
    let s = sqrt(max 0.0 (1.0-.x*.x)) in
    [|[|(x,0.0);(0.0,s)|];[|(0.0,s);(x,0.0)|]|] in
 
  (* Phase gate R(phi) = [[e^{i*phi},0],[0,e^{-i*phi}]] *)
  let r_mat phi =
    [|[|(cos phi, sin phi);(0.0,0.0)|];
      [|(0.0,0.0);(cos phi, -.sin phi)|]|] in
 
  (* 2x2 complex matrix multiply *)
  let mm a b =
    [|[|cadd(cmul a.(0).(0) b.(0).(0))(cmul a.(0).(1) b.(1).(0));
        cadd(cmul a.(0).(0) b.(0).(1))(cmul a.(0).(1) b.(1).(1))|];
      [|cadd(cmul a.(1).(0) b.(0).(0))(cmul a.(1).(1) b.(1).(0));
        cadd(cmul a.(1).(0) b.(0).(1))(cmul a.(1).(1) b.(1).(1))|]|] in
 
  (* Evaluate QSP unitary U(Φ, x): product R(phi_0)*W*R(phi_1)*...*R(phi_d) *)
  let eval_u phis x =
    let wx = w_mat x in
    let fwd = Array.make (2*n+1)
      [|[|(1.0,0.0);(0.0,0.0)|];[|(0.0,0.0);(1.0,0.0)|]|] in
    for k = 0 to d do
      let rk = r_mat phis.(k) in
      let after_r = mm fwd.(2*k) rk in
      fwd.(2*k+1) <- after_r;
      if k < d then fwd.(2*k+2) <- mm after_r wx
    done; fwd in
 
  (* Objective L(Φ) = sum_k (Re(U_{00}(x_k)) - f(x_k))^2 *)
  let objective phis =
    let total = ref 0.0 in
    Array.iteri (fun k xk ->
      let fwd = eval_u phis xk in
      let (pr,_) = fwd.(2*d+1).(0).(0) in
      let diff = pr -. ft.(k) in
      total := !total +. diff *. diff
    ) xs; !total in
 
  (* Gradient via forward-backward pass.
     ∂L/∂phi_j = 2 * sum_k (Re(U_00) - f_k) * ∂Re(U_00)/∂phi_j
     ∂U/∂phi_j = F_{j-1} * (i*Z * R(phi_j)) * B_{j+1}
     where i*Z*R(phi) = [[i*e^{i*phi},0],[0,-i*e^{-i*phi}]] *)
  let gradient phis =
    let g = Array.make n 0.0 in
    Array.iteri (fun k xk ->
      let fwd = eval_u phis xk in
      (* Backward products: bwd.(k) = product from gate k to end *)
      let bwd = Array.make (2*d+2)
        [|[|(1.0,0.0);(0.0,0.0)|];[|(0.0,0.0);(1.0,0.0)|]|] in
      let wx = w_mat xk in
      for j = d downto 0 do
        let rj = r_mat phis.(j) in
        bwd.(2*j+1) <- mm rj bwd.(2*j+2);
        if j > 0 then bwd.(2*j) <- mm wx bwd.(2*j+1)
        else bwd.(2*j) <- bwd.(2*j+1)
      done;
      let (u00,_) = fwd.(2*d+1).(0).(0) in
      let diff = 2.0 *. (u00 -. ft.(k)) in
      (* Derivative of R(phi_j): dR = i*Z*R(phi_j) = [[i*e^{ip}],[0,-i*e^{-ip}]] *)
      for j = 0 to d do
        let phi_j = phis.(j) in
        let dr = [|[|(-.sin phi_j, cos phi_j);(0.0,0.0)|];
                   [|(0.0,0.0);(sin phi_j, cos phi_j)|]|] in
        (* Contribution: F_{before_j} * dR * B_{after_j} *)
        let lft = if j = 0 then
          [|[|(1.0,0.0);(0.0,0.0)|];[|(0.0,0.0);(1.0,0.0)|]|]
        else fwd.(2*j) in
        let rgt = if j = d then
          [|[|(1.0,0.0);(0.0,0.0)|];[|(0.0,0.0);(1.0,0.0)|]|]
        else bwd.(2*j+2) in
        let mid = mm dr rgt in
        let full = mm lft mid in
        let (dr00,_) = full.(0).(0) in
        g.(j) <- g.(j) +. diff *. dr00
      done
    ) xs; g in
 
  (* L-BFGS with m=10 history vectors *)
  let m_hist = 10 in
  let phis = Array.make n 0.0 in
  (* Warm start: linear ramp heuristic *)
  Array.iteri (fun j _ ->
    phis.(j) <- (float_of_int j -. float_of_int d /. 2.0) *. pi /. float_of_int (d+2)
  ) phis;
 
  let ss = Array.make m_hist (Array.make n 0.0) in  (* s_k = phi_{k+1} - phi_k *)
  let ys = Array.make m_hist (Array.make n 0.0) in  (* y_k = g_{k+1} - g_k    *)
  let rhos = Array.make m_hist 0.0 in
  let hist_size = ref 0 in
  let hist_start = ref 0 in
  let prev_g = ref (Array.make n 0.0) in
 
  let dot a b = Array.fold_left2 (fun acc ai bi -> acc +. ai *. bi) 0.0 a b in
  let axpy a x y = Array.init (Array.length x) (fun i -> y.(i) +. a *. x.(i)) in
  let scale a x = Array.map (fun xi -> a *. xi) x in
 
  let max_iter = 200 in
  let _ = objective phis in  (* warm up *)
  for iter = 0 to max_iter - 1 do
    let g = gradient phis in
    (* L-BFGS two-loop recursion to get direction q *)
    let q = Array.copy g in
    let alphas = Array.make m_hist 0.0 in
    let h = !hist_size in
    for ii = 0 to h-1 do
      let i = (!hist_start + h - 1 - ii) mod m_hist in
      let a = rhos.(i) *. dot ss.(i) q in
      alphas.(ii) <- a;
      Array.iteri (fun j qj -> q.(j) <- qj -. a *. ys.(i).(j)) q
    done;
    (* Scale initial Hessian *)
    let scale_h = if h > 0 then
      let i = (!hist_start + h - 1) mod m_hist in
      dot ys.(i) ss.(i) /. (dot ys.(i) ys.(i) +. 1e-10)
    else 1.0 in
    let r = scale scale_h q in
    for ii = 0 to h-1 do
      let i = (!hist_start + ii) mod m_hist in
      let beta = rhos.(i) *. dot ys.(i) r in
      Array.iteri (fun j rj -> r.(j) <- rj +. ss.(i).(j) *. (alphas.(h-1-ii) -. beta)) r
    done;
    (* Line search: backtracking Armijo *)
    let step = ref (if iter = 0 then 0.1 else 1.0) in
    let f0 = objective phis in
    let gd = dot g r in
    let c1 = 1e-4 in
    let found = ref false in
    let ls_iter = ref 0 in
    while not !found && !ls_iter < 30 do
      let phi_new = axpy (-. !step) r phis in
      let f_new = objective phi_new in
      if f_new <= f0 -. c1 *. !step *. gd then begin
        let g_new = gradient phi_new in
        (* Update history *)
        let s_k = axpy (-. !step) r (Array.make n 0.0) in
        let y_k = Array.init n (fun j -> g_new.(j) -. g.(j)) in
        let sy = dot s_k y_k in
        if abs_float sy > 1e-10 then begin
          let idx = (!hist_start + !hist_size) mod m_hist in
          ss.(idx) <- s_k; ys.(idx) <- y_k;
          rhos.(idx) <- 1.0 /. sy;
          if !hist_size < m_hist then incr hist_size
          else hist_start := (!hist_start + 1) mod m_hist
        end;
        Array.blit phi_new 0 phis 0 n;
        prev_g := g_new;
        found := true
      end else begin
        step := !step *. 0.5;
        incr ls_iter
      end
    done;
    if not !found then begin
      (* Fallback: steepest descent step *)
      let gnorm = sqrt(dot g g) in
      if gnorm > 1e-12 then
        Array.iteri (fun j _ -> phis.(j) <- phis.(j) -. 1e-3 *. g.(j) /. gnorm) phis
    end;
    (* Early termination if gradient is small *)
    let _ = prev_g in
    if objective phis < err *. err *. float_of_int n then ()
  done;
  Array.to_list phis)".

(* total_order_T for R is expected to return 'bool option' in the Rdefinitions module context.
   Some true -> r1 < r2, None -> r2 < r1, Some false -> r1 = r2. *)
Extract Constant total_order_T => 
"(fun r1 r2 -> if r1 < r2 then Some true else if r2 < r1 then None else Some false)".

(* Map Q<->R with the generated QArith_base.ml *)
Extract Inlined Constant Coq.Reals.Rdefinitions.Q2R =>
"(fun q ->
   (Float.of_int q.QArith_base.coq_Qnum) /.
   (Float.of_int q.QArith_base.coq_Qden))".

(* Q is extracted over machine ints (ExtrOcamlZInt), and Coq's Qplus/Qmult never
   reduce, so VOQC's rotation merging multiplied denominators (1e9 -> 1e18 -> 1e27)
   and silently overflowed after a few merges, giving wrong angles. Return the
   gcd-reduced fraction instead: it is Qeq-equal to Coq's result (VOQC compares
   with Qeq_bool), and keeps denominators near 1e9. *)
Extract Constant Qplus =>
"(fun x y ->
   let rec gcd a b = if b = 0 then abs a else gcd b (a mod b) in
   let n = x.coq_Qnum * y.coq_Qden + y.coq_Qnum * x.coq_Qden in
   let d = x.coq_Qden * y.coq_Qden in
   let g = gcd n d in let g = if g = 0 then 1 else g in
   { coq_Qnum = n / g; coq_Qden = d / g })".
Extract Constant Qmult =>
"(fun x y ->
   let rec gcd a b = if b = 0 then abs a else gcd b (a mod b) in
   let n = x.coq_Qnum * y.coq_Qnum and d = x.coq_Qden * y.coq_Qden in
   let g = gcd n d in let g = if g = 0 then 1 else g in
   { coq_Qnum = n / g; coq_Qden = d / g })".

Extract Inlined Constant FullGateSet.R2Q =>
"(fun x ->
   let scale = 1000000000 in
   let n = int_of_float (Float.round (x *. Float.of_int scale)) in
   { QArith_base.coq_Qnum = n; QArith_base.coq_Qden = scale })".


(* Extracting the following to dummy values to supress warnings *)
Extract Constant ClassicalDedekindReals.sig_forall_dec  => "failwith ""Invalid extracted value"" ".
Extract Constant ClassicalDedekindReals.DRealRepr  => "failwith ""Invalid extracted value"" ".

(* map R->Nat to ocaml Float.ceil function *)
Extract Constant ceilR_N =>
"fun (r: float) ->
  let k = int_of_float (Float.ceil r) in
  if k <= 0 then 0 else k".

(* Extract from C to (float * float) *)
Require Import QuantumLib.Complex.
Extract Inlined Constant C => "(float * float)".
Extract Inlined Constant RtoC => "(fun x -> (x, 0.0))".
Extract Inlined Constant Ci => "(0.0, 1.0)".
Extract Inlined Constant Cmult => "(fun (a1, a2) (b1, b2) -> (a1 *. b1 -. a2 *. b2, a1 *. b2 +. a2 *. b1))".
Extract Inlined Constant Complex.Copp => "(fun (a, b) -> (-. a, -. b))".

(* Extract Random generators to Ocaml Random *)
Extract Inlined Constant random_float => "Random.float".
From QBlue Require Import QBlueMarQSim.
Extract Inlined Constant GenPgc => "Bridge.get_matrix_pgc".
Extract Constant nsampe_gatesize_est => "100".
Extract Constant ngates_per_chunk => "3000".
Extract Constant qdrift_sample_cap => "100000".


Set Extraction Optimize.
Cd "./extracted".
Separate Extraction
  QBlueSynth.check_2local

  QBlueTTS_v4.TTS_LCU1

  QBlueMarQSim.get_trans_CNOT
  QBlueMarQSim.get_trans_mixed
  QBlueMarQSim.get_trans_MarQdrift

  QBlueCompile.translate_highp2circ 
  QBlueCompile.translate_lowp2circ_stdTrotter 
  QBlueCompile.translate_lowp2circ_2ndTrotter 
  QBlueCompile.translate_lowp2circ_qdrift
  QBlueCompile.translate_lowp2circ_marqsim
  QBlueCompile.translate_lowp2circ_TTS_LCU
  QBlueCompile.translate_lowp2circ_qwalk
  QBlueCompile.translate_lowp2IndiAna_stdTrotter
  QBlueCompile.translate_lowp2IndiAna_2ndTrotter
  QBlueCompile.translate_lowp2IndiAna_qdrift
  QBlueCompile.translate_lowp2IndiAna_marqsim
  QBlueCompile.translate_lowp2IndiAna_TTS_LCU
  QBlueCompile.translate_lowp2IBMAna_stdTrotter
  QBlueCompile.translate_lowp2IBMAna_std_2ndTrotter
  QBlueCompile.translate_lowp2IBMAna_qdrift
  QBlueCompile.translate_lowp2IBMAna_marqsim
  QBlueCompile.translate_lowp2IBMAna_TTS_LCU
  QBlueQuantumWalk.build_qwalk_lcu_circuit
  QBlueQuantumWalk.build_state_prep
  QBlueQuantumWalk.build_inner_prep
  QBlueQuantumWalk.build_outer_prep
  QBlueQuantumWalk.findK_qwalk
  QBlueQubitization.findDegree_qsp
  QBlueQubitization.build_qubitization_circuit
  QBlueQSVT.findDegree_qsvt
  QBlueQSVT.build_qsvt_circuit
  QBlueQSVT_updateQSP.haah_qsp_solver
  QBlueQSVT_updateQSP.build_qsvt_circuit
  QBlueCompile.translate_lowp2circ_qsvt
  QBlueCompile.translate_lowp2circ_qsvt_updateQSP
  QBlueCompile.translate_lowp2IndiAna_qsvt_updateQSP
  QBlueCompile.translate_lowp2IBMAna_qsvt_updateQSP

(* gate decomposition pass *)
  ExtractionGateSet.decompose_to_voqc_gates

(* VOQC functions you want in the same local type universe *)
  QBlueSynthDigital.ibmdigi_to_rzq
  QBlueSynthDigital.ibmdigi_voqc_optimize
  QBlueSynthDigital.ibmdigi_to_rzq_a2a
  QBlueSynthDigital.ibmdigi_voqc_optimize_a2a
  QBlueSynthDigital.cvt_egate_fullgate
  QBlueSynthDigital.voqc_count_total
  QBlueSynthDigital.voqc_count_H
  QBlueSynthDigital.voqc_count_X
  QBlueSynthDigital.voqc_count_Rzq
  QBlueSynthDigital.voqc_count_CX
  QBlueSynthDigital.voqc_count_U1
  QBlueSynthDigital.voqc_count_U2
  QBlueSynthDigital.voqc_count_U3
  QBlueSynthDigital.voqc_convert_to_rzq
  QBlueSynthDigital.voqc_swap_route
  QBlueSynthDigital.voqc_decompose_swaps
  QBlueSynthDigital.voqc_optimize
  QBlueSynthDigital.voqc_make_lnn_ring
  QBlueSynthDigital.voqc_trivial_layout
  QBlueSynthDigital.voqc_lnn_ring_path_finding_fun.

 
 

