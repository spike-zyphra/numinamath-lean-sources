import Mathlib

theorem algebra_21742 : Complex.abs (-1 + Real.sqrt 3 * .I) = 2 := by
  simp [Complex.abs, Complex.normSq] 
  ring_nf
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num