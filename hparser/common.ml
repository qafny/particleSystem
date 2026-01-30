(* File: common.ml *)


type blueExp =
| HId
| HAnni
| HDag blueExp
| HPlus (blueExp * blueExp)
| HApp (blueExp * blueExp)
| HTensor ((float * float) * int -> blueExp)
