import Mathlib

theorem algebra_15683 (meter x y : ℝ) (hx : x = 24) (hy : y = 9 * meter - (9 * meter + 32)) :
    √(x ^ 2 + y ^ 2) = 40 := by
  have h1 : y = -32 := by
    linarith
  rw [hx, h1]
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  <;> ring_nf <;> norm_num
  all_goals norm_num