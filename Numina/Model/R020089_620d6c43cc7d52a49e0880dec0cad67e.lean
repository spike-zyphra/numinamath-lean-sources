import Mathlib

theorem algebra_11345 (a b c : ℝ) (ha : a ≠ 0) (h : a = -32) (h1 : b = 84) (h2 : c = 135) :
    (-b + √(b^2 - 4 * a * c)) / (2 * a) + (-b - √(b^2 - 4 * a * c)) / (2 * a) = 21 / 8 := by
  rw [h] at *
  rw [h1] at *
  rw [h2] at *
  have h3 : √(84 ^ 2 - 4 * (-32 : ℝ) * (135 : ℝ)) = 156 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  rw [h3]
  field_simp
  <;> norm_num [h3]