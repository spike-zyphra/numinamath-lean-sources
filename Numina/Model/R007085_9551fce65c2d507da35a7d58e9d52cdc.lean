import Mathlib

theorem algebra_17190 (x1 x2 y1 y2 : ℝ) (h1 : x1 = 2) (h2 : x2 = -6) (h3 : y1 = 5)
    (h4 : y2 > 0) (h5 : Real.sqrt ((x2 - x1)^2 + (y2 - y1)^2) = 10) :
    y2 = 11 := by
  rw [h1, h2, h3] at h5
  have h6 : Real.sqrt ((-6 - (2 : ℝ))^2 + (y2 - (5 : ℝ))^2) = 10 := h5
  have h7 : (-6 - (2 : ℝ))^2 + (y2 - (5 : ℝ))^2 = 100 := by
    calc 
      (-6 - (2 : ℝ))^2 + (y2 - (5 : ℝ))^2 = (Real.sqrt ((-6 - (2 : ℝ))^2 + (y2 - (5 : ℝ))^2)) ^ 2 := by 
        rw [Real.sq_sqrt]
        positivity
      _ = (10 : ℝ) ^ 2 := by rw [h6]
      _ = (100 : ℝ) := by norm_num
  norm_num at h7 
  have h8 : (y2 - 5)^2 = 36 := by 
    linarith 
  have h9 : (y2 - 5) = 6 ∨ (y2 - 5) = -6 := by 
    have h10 : (y2 - 5) ^ 2 = 36 := h8 
    have h11 : (y2 - 5 - 6) * (y2 - 5 + 6) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.mp h11) with h12 h13
    · 
      left 
      linarith 
    · 
      right 
      linarith 
  cases' h9 with h10 h11 
  · 
    linarith 
  · 
    have h12 : y2 = -1 := by linarith 
    linarith