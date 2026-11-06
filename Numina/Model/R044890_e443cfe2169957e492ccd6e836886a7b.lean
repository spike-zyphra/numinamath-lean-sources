import Mathlib
theorem number_theory_22783 : (Nat.ofDigits 3 [1,2,1]) +  (Nat.ofDigits 3 [2,2,1,2]) -
    (Nat.ofDigits 3 [0,0,2,1]) - (Nat.ofDigits 3 [1,1,1,2]) = -Nat.ofDigits 3 [1,2,2] := by 
  norm_num [Nat.ofDigits]