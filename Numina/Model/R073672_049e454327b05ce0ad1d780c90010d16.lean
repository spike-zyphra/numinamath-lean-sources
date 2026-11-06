import Mathlib

theorem algebra_174547 {m n b : ℝ} (h₀ : 0 < m) (h₁ : 0 < n) (h₂ : Real.logb 10 m = b - Real.logb 10 n) :
    m = 10 ^ b / n := by 
  have h₃ : m = (10 : ℝ) ^ (Real.logb 10 m) := by 
    field_simp [h₀.ne.symm]
  
  rw [h₂] at h₃
  
  have h₄ : (10 : ℝ) ^ (Real.logb 10 n) = n := by
    rw [Real.rpow_logb]
    all_goals linarith
    all_goals linarith
  
  have h₅ : (10 : ℝ) ^ (b - Real.logb 10 n) = (10 : ℝ) ^ b / ((10 : ℝ) ^ (Real.logb 10 n)) := by 
    rw [← Real.rpow_sub]
    ring_nf
    all_goals linarith
  
  rw [h₅] at h₃
  rw [h₄] at h₃
  
  simpa using h₃