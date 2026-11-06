import Mathlib

theorem number_theory_300932 : ¬(2005^3 - 2005 ≡ 0 [ZMOD 2003]) := by 
  norm_num [Int.ModEq]
  all_goals trivial