import Mathlib

theorem algebra_21023 : Complex.abs (Complex.ofReal (-324) + Complex.I * 243) = 405 := by
  simp [Complex.abs, Complex.normSq]
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num