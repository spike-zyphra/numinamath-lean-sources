import Mathlib

/- Simplify $\sqrt{25000}$. -/
theorem algebra_16548 : √25000 = 50 * √10 := by
  rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
  <;> ring_nf
  <;> norm_num
  <;> linarith