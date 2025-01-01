(* Define m, n, j, k as natural numbers (type alias for int) *)
type m = int  (* m is an alias for int *)
type n = int  (* n is an alias for int *)
type j = int  (* j is an alias for int *)
type k = int  (* k is an alias for int *)

(* Define a real number type as float *)
type real = float

(* Define a complex number type using a record *)
type complex = { re : float; im : float }

(* Alias 'complex' to 'z' *)
type z = complex  (* 'z' is an alias for the 'complex' type *)

(* Define x, y, f, g as string variables *)
type x = string  (* x is an alias for string *)
type y = string  (* y is an alias for string *)
type f = string  (* f is an alias for string *)
type g = string  (* g is an alias for string *)

(* Define a single site inner product *)
type v_dagger = complex * int list list (* Represents a complex number multiplied by a matrix *)

(* Define a single particle operator *)
type alpha = complex * int list list (* Represents a single particle operator *)

(* Define the arithmetic type *)
type xi = 
  | int        (* Represents natural numbers, i.e., type int *)
  | real       (* Represents real numbers, i.e., type float *)
  | complex    (* Represents complex numbers *)
  | xi         (* Represents function types xi to xi *)

(* Define the data type flag *)
type zeta = 
  | p    (* Represents ordinary matrix *)
  | h    (* Represents Hermitian matrix *)
  | u    (* Represents Unitary matrix *)

(* Define the quantum state type *)
type iota = 
  | T of int * int         (* Represents t(n, m) - single particle state *)
  | Tensor of iota * iota  (* Represents iota tensor with iota - tensor product of two quantum state *)

(* Define the quantum type *)
type tau = 
  | T of iota               (* Represents t(iota) *)
  | T_dagger of iota        (* Represents t_dagger(iota) *)
  | T Fun of (zeta * iota)  (* Represents F^zeta(iota) *)

(* Define the type *)
type omega = 
  | xi    (* Represents an arithmetic type (xi) *)
  | tau   (* Represents a quantum type (tau) *)
  | omega (* Represents a function type (omega to omega) *)

(* Define  the expression *)
type e =
  | Var of x               (* Variable x *)
  | Lambda of x * e        (* Lambda abstraction (lambda_x : omega. e) *)
  | Apply of e * e         (* Function application (e e) *)
  | Mu of x * e            (* Let binding (mu_f : omega. e) *)
  | psi of T of iota       (* Quantum state (psi : t(iota)) *)
  | alpha of T Fun of zeta * int * int    (* Operator (alpha : F^zeta(t(n,m))) *)
  | e_dagger of e          (* Adjoint (e_dagger) *)
  | Tensor of e * e        (* Tensor product (e and e) *)
  | Add of e + e           (* Addition (e + e) *)
  | Norm of e              (* Norm (nor(e)) *)


  (* Function to compute the Kronecker product (tensor product) of two matrices *)
let kronecker_product (a : float list list) (b : float list list) : float list list =
  let multiply_element a_ij b =
    (* Multiply each element of b by a_ij and return a new matrix *)
    List.map (fun row -> List.map (fun x -> a_ij *. x) row) b
  in

  (* Generate the Kronecker product by multiplying each element of `a` by matrix `b` *)
  List.flatten (List.map (fun row ->
    List.flatten (List.map (fun a_ij -> multiply_element a_ij b) row)
  ) a)
;;

(* Function to print matrices *)
let print_matrix mat =
  List.iter (fun row ->
    Printf.printf "[ ";
    List.iter (Printf.printf "%f ") row;
    Printf.printf "]\n"
  ) mat
;;

(* Example matrices *)
let a = [[1.0; 2.0]; [3.0; 4.0]]  (* 2x2 matrix *)
let b = [[5.0; 6.0]; [7.0; 8.0]]  (* 2x2 matrix *)

let result = kronecker_product a b;;

(* Print the tensor product result *)
let () =
  Printf.printf "Tensor product of matrices: \n";
  print_matrix result

(* General function to compute the Kronecker product of n matrices *)
let rec kronecker_product_n matrices =
  match matrices with
  | [] -> failwith "Empty matrix list"
  | [single_matrix] -> single_matrix  (* Base case: return the matrix as is *)
  | a :: b :: rest -> 
      let product_ab = kronecker_product a b in  (* Kronecker product of the first two matrices *)
      kronecker_product_n (product_ab :: rest)  (* Recursively apply to the remaining matrices *)

(* Helper function to compute the Kronecker product of two matrices *)
and kronecker_product (a : float list list) (b : float list list) : float list list =
  let multiply_element a_ij b =
    (* Multiply each element of b by a_ij and return a new matrix *)
    List.map (fun row -> List.map (fun x -> a_ij *. x) row) b
  in

  (* Generate the Kronecker product by multiplying each element of `a` by matrix `b` *)
  List.flatten (List.map (fun row ->
    List.flatten (List.map (fun a_ij -> multiply_element a_ij b) row)
  ) a)
;;

(* Example matrices *)
let a = [[1.0; 2.0]; [3.0; 4.0]]  (* 2x2 matrix *)
let b = [[5.0; 6.0]; [7.0; 8.0]]  (* 2x2 matrix *)
let c = [[9.0; 10.0]; [11.0; 12.0]]  (* 2x2 matrix *)

let matrices = [a; b; c]  (* List of matrices to compute the Kronecker product *)

let result = kronecker_product_n matrices;;

(* Print the tensor product result *)
let () =
  Printf.printf "Tensor product of matrices: \n";
  print_matrix result;;



(* Matrix type definition: a matrix is represented as a list of lists of floats. *)
type matrix = float list list

(* Convert a list of lists to an array of arrays *)
let list_to_array (m : matrix) : float array array =
  List.map (Array.of_list) m |> Array.of_list

(* Convert an array of arrays back to a list of lists *)
let array_to_list (m : float array array) : matrix =
  Array.to_list (Array.map Array.to_list m)

(* Compute the dot product of two lists (vectors) *)
let dot_product (v1 : float list) (v2 : float list) : float =
  List.fold_left2 (fun acc x y -> acc +. (x *. y)) 0.0 v1 v2

(* Matrix multiplication (using your array-based implementation) *)
let mult (m0 : matrix) (m1 : matrix) : matrix =
  let m0_arr = list_to_array m0 in
  let m1_arr = list_to_array m1 in

  let x0 = Array.length m0_arr and y0 = Array.length m0_arr.(0) in
  let x1 = Array.length m1_arr and y1 = Array.length m1_arr.(0) in

  if y0 <> x1 then failwith "incompatible matrices!" 
  else
    let res_matrix = Array.make_matrix x0 y1 0. in
    for i = 0 to x0 - 1 do
      for j = 0 to y1 - 1 do
        for k = 0 to y0 - 1 do
          res_matrix.(i).(j) <- res_matrix.(i).(j) +. m0_arr.(i).(k) *. m1_arr.(k).(j)
        done
      done
    done;
    array_to_list res_matrix  (* Convert the result back to list of lists *)

(* Helper function to add two matrices (assumes matrices have the same dimensions). *)
let add_matrices (m1 : matrix) (m2 : matrix) : matrix =
  let add_row r1 r2 = List.map2 ( +. ) r1 r2 in
  List.map2 add_row m1 m2

(* Add a list of matrices together. *)
let add (matrices : matrix list) : matrix =
  match matrices with
  | [] -> failwith "No matrices to add"
  | [m] -> m
  | m1 :: m2 :: rest -> 
      let rec add_rest m = function
        | [] -> m
        | m' :: ms -> add_rest (add_matrices m m') ms
      in
      add_rest (add_matrices m1 m2) rest

(* Multiply a list of matrices together. *)
let multiply (matrices : matrix list) : matrix =
  match matrices with
  | [] -> failwith "No matrices to multiply"
  | [m] -> m
  | m1 :: m2 :: rest -> 
      let rec multiply_rest m = function
        | [] -> m
        | m' :: ms -> multiply_rest (mult m m') ms
      in
      multiply_rest (mult m1 m2) rest

(* Print matrix for visualization *)
let print_matrix (m : matrix) : unit =
  let print_row row = 
    Printf.printf "[ ";
    List.iter (fun x -> Printf.printf "%.2f " x) row;
    Printf.printf "]\n"
  in
  List.iter print_row m

(* Example usage *)
let () =
  let a = [[1.0; 2.0]; [3.0; 4.0]] in
  let b = [[5.0; 6.0]; [7.0; 8.0]] in
  let c = [[9.0; 10.0]; [11.0; 12.0]] in
  
  (* Add matrices a, b, and c *)
  let added_matrices = add [a; b; c] in
  Printf.printf "Added matrices:\n";
  print_matrix added_matrices;

  (* Multiply matrices a, b, and c *)
  let multiplied_matrices = multiply [a; b; c] in
  Printf.printf "Multiplied matrices:\n";
  print_matrix multiplied_matrices;

  (* Dot product of two vectors *)
  let v1 = [1.0; 2.0; 3.0; 4.0] in
  let v2 = [4.0; 5.0; 6.0; 7.0] in
  let dp = dot_product v1 v2 in
  Printf.printf "Dot product of v1 and v2: %.2f\n" dp;;



  (* Type for a complex number represented as (real part, imaginary part) *)
type complex = float * float  (* (real part, imaginary part) *)
type matrix = complex array array  (* Matrix of complex numbers *)

(* Function to compute the complex conjugate of a matrix *)
let complex_conjugate (m: matrix) : matrix =
  let rows = Array.length m in
  let cols = Array.length m.(0) in
  let conjugated = Array.make_matrix rows cols (0.0, 0.0) in
  for i = 0 to rows - 1 do
    for j = 0 to cols - 1 do
      let (real, imag) = m.(i).(j) in
      conjugated.(i).(j) <- (real, -.imag)  (* Take the negative of the imaginary part *)
    done
  done;
  conjugated

(* Function to compute the transpose of a matrix *)
let transpose (m: matrix) : matrix =
  let rows = Array.length m in
  let cols = Array.length m.(0) in
  let transposed = Array.make_matrix cols rows (0.0, 0.0) in
  for i = 0 to rows - 1 do
    for j = 0 to cols - 1 do
      transposed.(j).(i) <- m.(i).(j)
    done
  done;
  transposed

(* Function to compute the complex conjugate transpose (Hermitian transpose) of a matrix *)
let complex_conjugate_transpose (m: matrix) : matrix =
  m |> complex_conjugate |> transpose

(* Function to print a complex matrix for visualization *)
let print_matrix (m: matrix) : unit =
  let print_complex (real, imag) =
    Printf.printf "(%.2f, %.2f) " real imag
  in
  Array.iter (fun row ->
    Array.iter print_complex row;
    Printf.printf "\n"
  ) m

(* Example usage *)
let () =
  (* Define a matrix of complex numbers *)
  let matrix = [|
    [|(10.0, -100.0); (2.0, -1.0)|];
    [|(3.0, -200.0); (4.0, -2.0)|]
  |] in
  
  (* Print the original matrix *)
  Printf.printf "Original matrix:\n";
  print_matrix matrix;
  
  (* Compute the complex conjugate transpose of the matrix *)
  let conj_transpose_matrix = complex_conjugate_transpose matrix in
  
  (* Print the conjugate transpose matrix *)
  Printf.printf "Complex conjugate transpose of the matrix:\n";
  print_matrix conj_transpose_matrix;;



  (* Type alias for complex numbers (real, imaginary) *)
type complex = float * float

(* Type alias for matrices of complex numbers *)
type matrix = complex array array

(* Helper function to multiply two complex numbers *)
let multiply_complex (a : complex) (b : complex) : complex =
  let (a_r, a_i) = a in
  let (b_r, b_i) = b in
  (* (a_r + i*a_i) * (b_r + i*b_i) = (a_r*b_r - a_i*b_i) + i(a_r*b_i + a_i*b_r) *)
  (a_r *. b_r -. a_i *. b_i, a_r *. b_i +. a_i *. b_r)

(* Helper function to multiply two matrices of complex numbers *)
let multiply_matrices (a : matrix) (b : matrix) : matrix =
  let rows_a = Array.length a and cols_a = Array.length a.(0) in
  let rows_b = Array.length b and cols_b = Array.length b.(0) in
  if cols_a <> rows_b then
    failwith "Matrix dimensions do not match for multiplication!";
  let result = Array.make_matrix rows_a cols_b (0.0, 0.0) in
  for i = 0 to rows_a - 1 do
    for j = 0 to cols_b - 1 do
      let sum_real, sum_imag =
        (* Calculate C_{ij} = sum(A_{ik} * B_{kj}) for k *)
        Array.fold_left (fun (r_acc, i_acc) k ->
          let (a_r, a_i) = a.(i).(k) in
          let (b_r, b_i) = b.(k).(j) in
          let real_part = a_r *. b_r -. a_i *. b_i in
          let imag_part = a_r *. b_i +. a_i *. b_r in
          (r_acc +. real_part, i_acc +. imag_part)
        ) (0.0, 0.0) (Array.init cols_a (fun k -> k))
      in
      result.(i).(j) <- (sum_real, sum_imag)
    done
  done;
  result

(* Helper function to add two matrices of complex numbers *)
let add_matrices (a : matrix) (b : matrix) : matrix =
  Array.map2 (fun row_a row_b ->
    Array.map2 (fun (r1, i1) (r2, i2) -> (r1 +. r2, i1 +. i2)) row_a row_b
  ) a b

(* Helper function to scale a matrix by a complex number *)
let scale_matrix (m : matrix) (scalar : complex) : matrix =
  let (scalar_r, scalar_i) = scalar in
  Array.map (fun row ->
    Array.map (fun (r, i) ->
      (* Multiply each element by the complex scalar *)
      (r *. scalar_r -. i *. scalar_i, r *. scalar_i +. i *. scalar_r)
    ) row
  ) m

(* Define the identity matrix I *)
let identity = [|
  [|(1.0, 0.0); (0.0, 0.0)|];  
  [|(0.0, 0.0); (1.0, 0.0)|]
|]

(* Define the Hamiltonian matrix H *)
let hamiltonian = [|
  [|(2.0, 1.0); (2.0, -1.0)|];  
  [|(2.0, 3.0); (2.0, 1.0)|]
|]

(* Compute the matrix exponential approximation exp(-i H t) using the first 5 terms of the Taylor series *)
let exp_neg_iHt (hamiltonian : matrix) (t : float) : matrix =
  let i = (0.0, 1.0) in  (* Imaginary unit i as (0, 1) *)

  (* Compute the powers of H *)
  let h2 = multiply_matrices hamiltonian hamiltonian in  (* H^2 *)
  let h3 = multiply_matrices hamiltonian h2 in           (* H^3 *)
  let h4 = multiply_matrices h2 h2 in                    (* H^4 *)

  (* Initialize the result with the identity matrix (Term 1) *)
  let result = ref identity in

  (* Term 2: -i H t *)
  let term_2 = scale_matrix hamiltonian (0.0, -.t) in
  result := add_matrices !result term_2;

  (* Term 3: -(1/2) H^2 t^2 *)
  let term_3 = scale_matrix h2 (-.t *. t /. 2.0, 0.0) in
  result := add_matrices !result term_3;

  (* Term 4: (i/6) H^3 t^3 *)
  let term_4 = scale_matrix h3 (0.0, t *. t *. t /. 6.0) in
  result := add_matrices !result term_4;

  (* Term 5: (1/24) H^4 t^4 *)
  let term_5 = scale_matrix h4 (t *. t *. t *. t /. 24.0, 0.0) in
  result := add_matrices !result term_5;

  !result  (* Return the final result after adding the terms *)

(* Compute H^2, H^3, and H^4 directly for verification *)
let compute_powers () =
  let h2 = multiply_matrices hamiltonian hamiltonian in
  let h3 = multiply_matrices h2 hamiltonian in
  let h4 = multiply_matrices h2 h2 in
  (* Print the computed H^2, H^3, H^4 *)
  Printf.printf "H^2 = \n";
  Array.iter (fun row ->
    Array.iter (fun (r, i) -> Printf.printf "(%.3f, %.3f) " r i) row;
    Printf.printf "\n"
  ) h2;

  Printf.printf "\nH^3 = \n";
  Array.iter (fun row ->
    Array.iter (fun (r, i) -> Printf.printf "(%.3f, %.3f) " r i) row;
    Printf.printf "\n"
  ) h3;

  Printf.printf "\nH^4 = \n";
  Array.iter (fun row ->
    Array.iter (fun (r, i) -> Printf.printf "(%.3f, %.3f) " r i) row;
    Printf.printf "\n"
  ) h4

(* Example usage *)
let () =
  compute_powers ();
  let t = 1.0 in  (* Example time input *)
  let exp_Ht = exp_neg_iHt hamiltonian t in
  
  (* Print the result of exp(-i H t) *)
  Printf.printf "\nExp(-i H t) for H = \n";
  Array.iter (fun row ->
    Array.iter (fun (r, i) -> Printf.printf "(%.3f, %.3f) " r i) row;
    Printf.printf "\n"
  ) exp_Ht



  (* Define the state type as an integer representing the quantum number n_j *)
type state = int

(* Creation operator: a_dagger_j |n_j> = sqrt(n_j + 1) * |n_j + 1> *)
let create (n_j: state) : float * state =
  match n_j with
  | _ -> (* Wildcard pattern matching *)
      let factor = sqrt (float_of_int (n_j + 1)) in
      let new_state = n_j + 1 in
      Printf.printf "create function evaluated: sqrt(%d + 1) * |%d> -> %f * |%d>\n"
        n_j (n_j + 1) factor new_state;
      (factor, new_state)

(* Example function to demonstrate applying the creation operator *)
let example_create () =
  (* Start with state |24> *)
  let n_j = 24 in
  Printf.printf "Starting state: |%d>\n" n_j;

  (* Apply the creation operator using pattern matching with wildcard _ *)
  let _ = create n_j in
  (* No need to print the creation message again *)

  (* Force flushing of output to ensure it's printed immediately *)
  flush stdout;;

(* Run the example *)
example_create ();;



(* Define the state type as an integer representing the quantum number n_j *)
type state = int

(* Annihilation operator: a_j |n_j> = sqrt(n_j) * |n_j - 1> *)
let annihilate (n_j: state) : (float * state) option =
  match n_j with
  | 0 -> None  (* Cannot annihilate the vacuum state |0> *)
  | _ -> 
      let factor = sqrt (float_of_int n_j) in
      let new_state = n_j - 1 in
      Printf.printf "Annihilation operator applied: sqrt(%d) * |%d> -> %f * |%d>\n"
        n_j (n_j - 1) factor new_state;
      Some (factor, new_state)

(* Example function to demonstrate applying the annihilation operator *)
let example_annihilate () =
  (* Start with state |1> *)
  let n_j = 1 in
  Printf.printf "Starting state: |%d>\n" n_j;

  (* Apply the annihilation operator *)
  match annihilate n_j with
  | Some (factor, new_state) -> 
      (* The print is already done in the annihilate function, so we don't need another print here *)
      ()
  | None -> Printf.printf "Annihilation operator cannot be applied to the vacuum state.\n";

  (* Force flushing of output to ensure it's printed immediately *)
  flush stdout;;

(* Run the example *)
example_annihilate ();;



(* Define the state type as an integer representing the quantum number n_j *)
type state = int

(* Define the tensor product state as a list of states (each integer represents |n_j>) *)
type tensor_state = state list  (* A list representing the tensor product of states |j_k> *)

(* Define the annihilation operator for a single mode a_k (mode indexed by k) *)
let annihilate_mode (k: int) (state: state) : (float * state) option =
  match state with
  | 0 -> None  (* Cannot annihilate the vacuum state |0> *)
  | _ -> 
      let factor = sqrt (float_of_int state) in
      let new_state = state - 1 in
      Some (factor, new_state)

(* Apply the annihilation operator to the tensor product state, specifically to the mode indexed by k *)
let annihilate (k: int) (v: tensor_state) : (float * tensor_state) option =
  if k < 0 || k >= List.length v then
    None  (* Invalid mode index *)
  else
    (* Apply the annihilation operator only to the mode at index k *)
    let new_state_with_factors =
      List.mapi (fun index current_state ->
        if index = k then
          match annihilate_mode k current_state with
          | Some (factor, new_state) -> Some (factor, new_state)
          | None -> None  (* If annihilation is not possible, return None for this mode *)
        else
          Some (1.0, current_state)  (* Keep unchanged states as is *)
      ) v
    in
    (* If any mode's annihilation fails, return None *)
    if List.exists (fun x -> x = None) new_state_with_factors then
      None
    else
      (* Accumulate the factor and states correctly *)
      let factor, new_tensor_state =
        List.fold_left (fun (factor_acc, states_acc) opt ->
          match opt with
          | Some (factor_val, new_state) -> 
              (factor_acc *. factor_val, new_state :: states_acc)
          | None -> (factor_acc, states_acc)  (* This should never happen due to the check above *)
        ) (1.0, []) new_state_with_factors
      in
      Some (factor, List.rev new_tensor_state)

(* Helper function to convert a state to ket notation *)
let ket_notation state =
  Printf.sprintf "|%d>" state

(* Helper function to convert a tensor state to the full ket notation *)
let tensor_ket_notation state =
  String.concat " ⊗ " (List.map ket_notation state)

(* Example function to demonstrate applying annihilation to a state vector with user-defined mode k *)
let example_annihilate () =
  (* Define the state v as a tensor product of states |3>, |2>, |1> *)
  let v = [3; 2; 1] in  (* tensor product of |3> ⊗ |2> ⊗ |1> *)

  (* Print the starting state *)
  Printf.printf "Starting state: %s\n" (tensor_ket_notation v);

  (* Get the mode index from the user (let's assume valid input for simplicity) *)
  Printf.printf "Enter the mode index (0-based) to apply the annihilation operator: ";
  let k = read_int () in

  (* Check if the user input is within the valid range *)
  if k < 0 || k >= List.length v then
    Printf.printf "Error: The mode index %d is out of range. Please enter a value between 0 and %d.\n" k (List.length v - 1)
  else
    (* Apply the annihilation operator to the specified mode k *)
    match annihilate k v with
    | Some (factor, new_state) -> 
        (* Print the final state with the factor outside the ket *)
        Printf.printf "After annihilation on mode %d: sqrt(%d) * %s\n" 
          k (List.nth v k) (tensor_ket_notation new_state)
    | None -> Printf.printf "Annihilation could not be applied to the specified mode.\n";

  (* Force flushing of output to ensure it's printed immediately *)
  flush stdout;;

(* Run the example *)
example_annihilate ();;



(* Define the state type as an integer representing the quantum number n_j *)
type state = int

(* Define the tensor product state as a list of states (each integer represents |n_j>) *)
type tensor_state = state list  (* A list representing the tensor product of states |j_k> *)

(* Define the creation operator for a single mode j_k *)
let create_mode (state: state) : (float * state) option =
  if state < 0 then
    None  (* Creation cannot apply to a negative state, since n must be >= 0 *)
  else 
    let factor = sqrt (float_of_int (state + 1)) in
    let new_state = state + 1 in
    Some (factor, new_state)

(* Apply the creation operator to the tensor product state, specifically to the mode at index mode_index *)
let create (mode_index: int) (v: tensor_state) : (float * tensor_state) option =
  if mode_index < 0 || mode_index >= List.length v then
    None  (* Invalid mode index *)
  else
    (* Apply the creation operator only to the mode at index mode_index *)
    let new_state_with_factors =
      List.mapi (fun index current_state ->
        if index = mode_index then
          match create_mode current_state with
          | Some (factor, new_state) -> Some (factor, new_state)
          | None -> None  (* If creation is not possible, return None for this mode *)
        else
          Some (1.0, current_state)  (* Keep unchanged states as is *)
      ) v
    in
    (* If any mode's creation fails, return None *)
    if List.exists (fun x -> x = None) new_state_with_factors then
      None
    else
      (* Accumulate the factor and states correctly *)
      let factor, new_tensor_state =
        List.fold_left (fun (factor_acc, states_acc) opt ->
          match opt with
          | Some (factor_val, new_state) -> 
              (factor_acc *. factor_val, new_state :: states_acc)
          | None -> (factor_acc, states_acc)  (* This should never happen due to the check above *)
        ) (1.0, []) new_state_with_factors
      in
      (* Return the accumulated factor and new tensor state *)
      Some (factor, List.rev new_tensor_state)

(* Helper function to convert a state to ket notation *)
let ket_notation state =
  Printf.sprintf "|%d>" state

(* Helper function to convert a tensor state to the full ket notation *)
let tensor_ket_notation state =
  String.concat " ⊗ " (List.map ket_notation state)

(* Example function to demonstrate applying creation to a state vector with user-defined mode k *)
let example_create () =
  (* Define the state v as a tensor product of states |1>, |2>, |1> *)
  let v = [1; 2; 1] in  (* tensor product of |1> ⊗ |2> ⊗ |1> *)

  (* Print the starting state *)
  Printf.printf "Starting state: %s\n" (tensor_ket_notation v);

  (* Get the mode index from the user (let's assume valid input for simplicity) *)
  Printf.printf "Enter the mode index (0-based) to apply the creation operator: ";
  let k = read_int () in

  (* Check if the user input is within the valid range *)
  if k < 0 || k >= List.length v then
    Printf.printf "Error: The mode index %d is out of range. Please enter a value between 0 and %d.\n" k (List.length v - 1)
  else
    (* Apply the creation operator to the specified mode k *)
    match create k v with
    | Some (factor, new_state) -> 
        (* Print the final state with the factor outside the ket *)
        Printf.printf "After creation on mode %d: sqrt(%d) * %s\n" 
          k (List.nth v k + 1) (tensor_ket_notation new_state)
    | None -> Printf.printf "Creation could not be applied to the specified mode.\n";

  (* Force flushing of output to ensure it's printed immediately *)
  flush stdout;;

(* Run the example *)
example_create ();;