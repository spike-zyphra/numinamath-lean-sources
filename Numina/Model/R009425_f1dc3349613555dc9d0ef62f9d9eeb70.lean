import Mathlib

theorem number_theory_47463 : IsSquare (Nat.ofDigits 10 (5 :: List.replicate 1998 2 ++ List.replicate 1997 1)) := by 
  native_decide