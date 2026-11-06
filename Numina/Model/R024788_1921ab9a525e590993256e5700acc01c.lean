import Mathlib

theorem algebra_221654 {x y : ℝ} (h : x^2 + y^2 + x^2 * y^2 - 4 * x * y + 1 = 0) :
    (x + y)^2 = 4 := by 
  have h1 : (x - y) ^ 2 + (x * y - 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x * y - 1)]
  have h2 : (x - y) ^ 2 = 0 := by 
    linarith [sq_nonneg (x - y), sq_nonneg (x * y - 1)]
  have h3 : x - y = 0 := by 
    nlinarith [sq_nonneg (x - y)]
  have h4 : (x * y - 1)^2 = 0 := by 
    linarith [sq_nonneg (x - y), sq_nonneg (x * y - 1)]
  have h5 : x * y - 1 = 0 := by 
    nlinarith [sq_nonneg (x * y - 1)]
  have h6 : y = x := by linarith 
  have h7 : x * y = 1 := by linarith 
  have h8 : x^2 = 1 := by 
    have eq1 : x * y = 1 := by linarith 
    rw [show y = x by linarith] at eq1 
    nlinarith 
  calc 
    (x + y)^2 = (x + x)^2 := by rw [show y = x by linarith]
    _ = (2 * x)^2 := by ring
    _ = 4 * x^2 := by ring
    _ = 4 * (1) := by rw [h8]
    _ = 4 := by norm_num