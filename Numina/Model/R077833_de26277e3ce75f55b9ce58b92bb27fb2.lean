import Mathlib

theorem algebra_284630 (m : ℝ) (a b : ℝ × ℝ)
    (ha : a = (2 ^ m, -1)) (hb : b = (2 ^ m - 1, 2 ^ (m + 1)))
    (h : a.1 * b.1 + a.2 * b.2 = 0) :
    Real.sqrt (a.1 ^ 2 + a.2 ^ 2) = Real.sqrt 10 := by 
  rw [ha, hb] at h
  have h_eq : (2:ℝ) ^ m * (2 ^ m - 1) + (-1) * (2 ^ (m + 1)) = 0 := by 
    simpa using h
  have h1 : (2:ℝ) ^ (m + 1) = (2:ℝ) ^ m * 2 := by 
    rw [Real.rpow_add]
    norm_num
    all_goals linarith 
  rw [h1] at h_eq 
  have h3 : (2:ℝ) ^ m * (2 ^ m - 3) = 0 := by 
    nlinarith 
  have h4 : (2:ℝ) ^ m > 0 := by 
    positivity 
  have h5 : (2:ℝ) ^ m - 3 = 0 := by 
    nlinarith [h3, h4] 
  have h6 : (2:ℝ) ^ m = 3 := by 
    linarith 
  rw [ha]
  have h8 : ((2:ℝ) ^ m) ^ 2 + (-1:ℝ) ^ 2 = 10 := by 
    rw [h6] 
    norm_num 
  rw [h8]
  all_goals norm_num