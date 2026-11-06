import Mathlib

theorem algebra_21513 : (Nat.floor (10^5 * (31 / 11111 : ℝ)) % 100000) / 10^5 = 31 / 11111 := by
  norm_num [Nat.floor_eq_iff]