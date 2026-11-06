import Mathlib

/- Simplify $\sqrt{242}$. -/
theorem algebra_18779 : Real.sqrt 242 = 11 * Real.sqrt 2 := by 
  rw [Real.sqrt_eq_iff_sq_eq] <;>
  ring_nf <;>
  norm_num