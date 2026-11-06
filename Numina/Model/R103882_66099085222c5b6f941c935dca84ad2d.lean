import Mathlib

theorem algebra_16111 {a b c : ℝ} (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
    (h₃ : a^2 + b^2 = c^2) (h₄ : a = b) (h₅ : c = 4 * Real.sqrt 2) :
    (1 / 2) * a * b = 8 := by

  have h6 : a = b := h₄

  have h7 : a^2 + b^2 = c^2 := h₃

  rw [show b = a by linarith [h6]] at h7

  have h8 : 2 * a^2 = c^2 := by
    nlinarith
  
  have h9 : c = 4 * Real.sqrt 2 := h₅
  
  have h10 : 2 * a^2 = (4 * Real.sqrt 2) ^ 2 := by 
    rw [h9] at h8 
    linarith

  have h11 : (4 * Real.sqrt 2 : ℝ) ^ 2 = 32 := by
    calc
      (4 * Real.sqrt 2 : ℝ) ^ 2 = 4^2 * (Real.sqrt 2)^2 := by ring
      _ = 16 * (Real.sqrt 2)^2 := by norm_num
      _ = 16 * 2 := by rw [Real.sq_sqrt]; linarith [Real.sqrt_nonneg 2]
      _ = 32 := by norm_num
  
  rw [h11] at h10

  have h12 : a^2 = 16 := by 
    nlinarith
  
  have h13 : a = 4 := by 
    nlinarith [h₀]
  
  have h14 : b = 4 := by
    rw [show b = a by linarith [h6]]
    linarith [h13]

  rw [h13, h14]
  all_goals norm_num