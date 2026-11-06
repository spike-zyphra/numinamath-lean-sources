import Mathlib

theorem algebra_296525 {x y : ℝ} (h1 : (x + 1) * (y + 1) = 6) (h2 : x ^ 2 * y + x * y ^ 2 = 6) :
    x ^ 2 + y ^ 2 = 5 := by 
  have h3 : x * y + x + y = 5 := by 
    linarith [h1]
  have eq3 : x + y = 5 - x * y := by linarith
  have eq4 : x * y * (x + y) = 6 := by
    have h4 : x^2 * y + x * y^2 = x * y * (x + y) := by ring
    rw [h4] at h2
    linarith
  rw [eq3] at eq4
  have h5 : (x * y) ^ 2 - 5 * (x * y) + 6 = 0 := by 
    nlinarith 
  have h6 : (x * y - 2) * (x * y - 3) = 0 := by
    nlinarith 
  cases' (mul_eq_zero.mp h6) with h7 h8
  · 
    have hxy2 : x * y = 2 := by linarith
    have hxy_sum2 : x + y = 3 := by
      nlinarith
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 3), sq_nonneg (x * y - 2)]
  · 
    have hxy3 : x * y = 3 := by linarith 
    have hxy_sum1 : x + y = 2 := by 
      nlinarith
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 2), sq_nonneg (x * y - 3)]