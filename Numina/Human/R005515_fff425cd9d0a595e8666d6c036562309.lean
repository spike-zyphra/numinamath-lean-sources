import Mathlib

/-
A computer program is a function that takes in 4 bits, where each bit is either a 0 or a 1 , and outputs TRUE or FALSE. How many computer programs are there?
-/
theorem combinatorics_608585 : Fintype.card ((Fin 4 → Bool) → Bool) = 65536 := by
  norm_num [Fintype.card_fun]