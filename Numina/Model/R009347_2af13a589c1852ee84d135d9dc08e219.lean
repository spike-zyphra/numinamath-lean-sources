import Mathlib

theorem number_theory_15370 : Nat.ofDigits 2 (List.replicate 8 1) + Nat.ofDigits 2 (List.replicate 6 1) = 318 := by 
  norm_num [Nat.ofDigits, List.replicate, List.foldl]