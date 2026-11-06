import Mathlib

theorem number_theory_11245 : (Nat.digits 3 987).length = (Nat.digits 8 987).length + 3 := by
  norm_num