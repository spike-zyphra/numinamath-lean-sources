import Mathlib

theorem algebra_16902 : Complex.abs (-4 + (7 / 6) * .I) = 25 / 6 := by
  simp [Complex.abs, Complex.normSq]
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  all_goals norm_num