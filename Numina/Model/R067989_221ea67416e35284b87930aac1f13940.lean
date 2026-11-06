import Mathlib

theorem algebra_100746 (x : ℝ) (h : Real.sin x + Real.cos x = Real.sqrt 2 / 2) :
    (Real.sin x)^3 + (Real.cos x)^3 = 5 * Real.sqrt 2 / 8 := by 
  have h1 : (Real.sin x)^3 + (Real.cos x)^3 = (Real.sin x + Real.cos x) * ((Real.sin x)^2 - Real.sin x * Real.cos x + (Real.cos x)^2) := by 
    ring
  rw [h1, h]
  have h2 : (Real.sin x)^2 + (Real.cos x)^2 = 1 := Real.sin_sq_add_cos_sq x
  have h3 : Real.sin x * Real.cos x = -1 / 4 := by 
    have h4 : (Real.sin x + Real.cos x)^2 = (Real.sqrt 2 / 2)^2 := by 
      rw [h]
    have h5 : (Real.sin x + Real.cos x)^2 = (Real.sin x)^2 + (Real.cos x)^2 + 2 * (Real.sin x * Real.cos x) := by 
      ring
    rw [h5] at h4 
    have h6 : (Real.sqrt 2 / 2 : ℝ) ^ 2 = 1 / 2 := by 
      calc
        (Real.sqrt 2 / 2 : ℝ) ^ 2 = (Real.sqrt 2 ^ 2) / 4 := by ring
        _ = (2) / 4 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        _ = (1 : ℝ) / 2 := by norm_num
    rw [h6] at h4 
    have h7 : (Real.sin x)^2 + (Real.cos x)^2 = 1 := h2 
    rw [h7] at h4 
    linarith 
  have h4 : (Real.sin x)^2 - Real.sin x * Real.cos x + (Real.cos x)^2 = 5 / 4 := by 
    have h5 : (Real.sin x)^2 + (Real.cos x)^2 = 1 := h2 
    have h6 : Real.sin x * Real.cos x = -1 / 4 := h3 
    linarith 
  rw [h4]
  have h7 : Real.sqrt 2 / 2 * (5 / 4 : ℝ) = 5 * Real.sqrt 2 / 8 := by 
    ring 
  linarith [h7]