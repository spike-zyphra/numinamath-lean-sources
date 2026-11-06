import Mathlib

theorem algebra_136970 (x y : ℝ) (h₀ : x - y = 0) (h₁ : x^2 + y^2 - 6 * y = 0) :
    x^2 = 3 * y := by 
  have h2 : x = y := by linarith 
  rw [show y = x by linarith [h2]] at h₁
  have h4 : 2 * x^2 - 6 * x = 0 := by 
    nlinarith 
  have h5 : x^2 = 3 * x := by 
    linarith 
  -- Since x = y, so 3x = 3y 
  have h6 : 3 * x = 3 * y := by 
    linarith [h2] 
  linarith [h5, h6]