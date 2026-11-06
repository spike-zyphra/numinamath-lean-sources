import Mathlib

theorem number_theory_310853 : (7^2004 + 36)^818 ≡ 9 [MOD 10] := by
  norm_num [Nat.ModEq]