import Mathlib

theorem algebra_110573 {a b : ℝ} (ha : 0 < b) (hb : b < a) (h : a^2 + b^2 = 6 * a * b) :
    (a + b) / (a - b) = Real.sqrt 2 := by 
  have h1 : 0 < a := by nlinarith 
  have h2 : (a + b) ^ 2 = 8 * a * b := by 
    nlinarith 
  have h3 : (a - b) ^ 2 = 4 * a * b := by 
    nlinarith 
  have h4 : (a - b) ≠ 0 := by linarith 
  have h5 : ((a + b) / (a - b)) ^ 2 = 2 := by 
    field_simp [h4] 
    nlinarith [h2, h3]
  have h6 : 0 ≤ (a + b) / (a - b) := by 
    apply div_nonneg 
    all_goals linarith 
  have h7 : Real.sqrt (((a + b) / (a - b)) ^ 2) = (a + b) / (a - b) := by 
    rw [Real.sqrt_sq (show 0 ≤ (a + b) / (a - b) by linarith [h6]) ]
  have h8 : Real.sqrt (((a + b) / (a - b)) ^ 2) = Real.sqrt (2 : ℝ) := by 
    rw [h5] 
  rw [h7] at h8 
  nlinarith [h8]