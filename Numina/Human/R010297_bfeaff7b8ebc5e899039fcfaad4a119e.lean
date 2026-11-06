import Mathlib

/- Simplify $\sqrt{7\cdot 2}\cdot \sqrt{2^3\cdot 7^3}$. -/
theorem algebra_17044 : Real.sqrt (7 * 2) * Real.sqrt (2^3 * 7^3) = 196 := by
  rw [← Real.sqrt_mul] <;> norm_num <;> simp [Real.sqrt_eq_iff_sq_eq] <;> norm_num