import Mathlib

theorem algebra_13777 (a b : ℝ) (ha : a = 20) (hb : b = 10) :
    2 * √(a^2 - b^2) = 20 * √3 := by
  rw [ha, hb]
  have h1 : √((20 : ℝ) ^ 2 - (10 : ℝ) ^ 2) = 10 * √3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
    <;> ring_nf
    <;> norm_num
  rw [h1]
  all_goals ring_nf
  <;> norm_num