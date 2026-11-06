import Mathlib

theorem algebra_5074 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : x = y - 9) (h2 : 1 / x + 1 / y = 1 / 20) :
    x = 36 := by
  have h3 : y = x + 9 := by 
    nlinarith
  rw [h3] at h2
  have h4 : x ≠ 0 := by linarith
  have h5 : x + 9 > 0 := by 
    nlinarith
  have h5' : x + 9 ≠ 0 := by 
    linarith
  field_simp [(show x ≠ 0 by linarith), (show x + 9 ≠ 0 by nlinarith)] at h2
  have h6 : x ^ 2 - 31 * x - 180 = 0 := by 
    nlinarith
  have h7 : (x - 36) * (x + 5) = 0 := by 
    nlinarith
  cases' (mul_eq_zero.1 h7) with h8 h9
  · -- x - 36 = 0, so x = 36
    linarith
  · -- x + 5 = 0, so x = -5, but x > 0, contradiction
    nlinarith