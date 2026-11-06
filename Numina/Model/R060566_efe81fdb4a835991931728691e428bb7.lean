import Mathlib

theorem algebra_1004 {x y : ℝ} (h1 : x - y = 2) (h2 : x ^ 2 + y ^ 2 = 4) :
    x ^ 1992 + y ^ 1992 = 2 ^ 1992 := by
  have h3 : x * y = 0 := by
    have h4 : (x - y) ^ 2 = 4 := by 
      rw [h1]
      norm_num
    have h5 : (x - y) ^ 2 = x^2 + y^2 - 2 * (x * y) := by
      ring
    rw [h4, h2] at h5
    linarith
  cases (mul_eq_zero.mp h3) with
  | inl hx0 =>
    have hy1 : y = -2 := by
      linarith [h1, hx0]
    rw [hx0, hy1]
    norm_num
  | inr hy0 =>
    have hx1 : x = 2 := by
      linarith [h1, hy0]
    rw [hx1, hy0]
    norm_num