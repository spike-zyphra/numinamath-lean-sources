import Mathlib

/- Simplify $\sqrt{180}$. -/
theorem algebra_14532 : Real.sqrt 180 = 6 * Real.sqrt 5 := by
  rw [Real.sqrt_eq_iff_mul_self_eq] <;>
  ring_nf <;>
  norm_num