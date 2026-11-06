import Mathlib

/- Simplify $\sqrt{720}$. -/
theorem algebra_20708 : Real.sqrt 720 = 12 * Real.sqrt 5 := by 
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num [sq] <;> ring_nf <;> norm_num