import Mathlib

theorem algebra_198660 (x y : ℝ) (h₀ : x^2 + 3 * x * y - y^2 = 27) (h₁ : 3 * x^2 - x * y + y^2 = 27) :
    y ≤ 3 := by
  have h2 : 4 * x^2 + 2 * x * y = 54 := by
    nlinarith
  have h3 : -2 * x^2 + 4 * x * y - 2 * y^2 = 0 := by
    nlinarith
  have h4 : (x - y) ^ 2 = 0 := by
    nlinarith
  have h5 : x - y = 0 := by
    rwa [sq_eq_zero_iff] at h4
  have h6 : x = y := by linarith
  have h7 : 6 * x^2 = 54 := by
    rw [show y = x by linarith [h6]] at h2
    nlinarith
  have h8 : x^2 = 9 := by 
    nlinarith
  have h9 : x ≤ 3 := by 
    nlinarith [sq_nonneg (x - 3), sq_nonneg (x + 3)]
  have h10 : y ≤ 3 := by 
    nlinarith [h6, h9]
  linarith