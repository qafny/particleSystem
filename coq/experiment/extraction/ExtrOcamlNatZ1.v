Require Import QBlue.QBlueUtility.

Require Import ExtrOcamlNatInt.  
Require Import ExtrOcamlZInt.    

Extract Constant ceilR_N =>
"fun (r: float) ->
  let k = int_of_float (Float.ceil r) in
  if k <= 0 then 0 else k".
