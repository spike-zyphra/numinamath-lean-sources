import Mathlib

/- Simplify $\sqrt{245}$. -/
theorem algebra_15496 : Real.sqrt 245 = 7 * Real.sqrt 5 := by
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num <;> ring_nf <;> norm_num