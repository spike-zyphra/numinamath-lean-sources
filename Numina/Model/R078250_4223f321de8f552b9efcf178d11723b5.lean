import Mathlib

theorem algebra_10353 : ⌊|(-34.1 : ℝ)|⌋ = 34 := by
  norm_num [Int.floor_eq_iff, abs_of_nonneg, abs_of_nonpos]