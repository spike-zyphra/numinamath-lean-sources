import Mathlib

/- Simplify $\sqrt{288}$. -/
theorem algebra_16017 : √288 = 12 * √2 := by
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num <;> ring_nf <;> norm_num