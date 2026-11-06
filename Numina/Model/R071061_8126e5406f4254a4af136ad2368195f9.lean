import Mathlib

theorem algebra_5952 {x y : ℝ} (h : abs (2 * y - x - 11) + (3 * x - 4 * y + 25) ^ 6 = 0) :
    x = -3 := by
  have h1 : abs (2 * y - x - 11) ≥ 0 := abs_nonneg (2 * y - x - 11)
  have h2 : (3 * x - 4 * y + 25) ^ 6 ≥ 0 := by positivity

  have h3 : abs (2 * y - x - 11) = 0 := by linarith
  have h4 : (3 * x - 4 * y + 25) ^ 6 = 0 := by linarith
  
  have h5 : 2 * y - x - 11 = 0 := by
    rwa [abs_eq_zero] at h3
  
  have h6 : 3 * x - 4 * y + 25 = 0 := by 
    apply pow_eq_zero 
    exact h4
  
  linarith [h5, h6]