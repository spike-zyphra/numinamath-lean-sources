import Mathlib

theorem algebra_100962 (a b c d e f : ℝ) (h₀ : a ≥ b ∧ b ≥ c ∧ c ≥ d ∧ d ≥ e ∧ e ≥ f)
    (h₁ : (a + b + c + d + e + f - a) / 5 = (a + b + c + d + e + f) / 6 - 1)
    (h₂ : (a + b + c + d + e + f - f) / 5 = (a + b + c + d + e + f) / 6 + 1)
    (h₃ : (a + b + c + d + e + f - a - f) / 4 = 20) :
    a * f = 375 := by 
  have h5 : a + b + c + d + e + f = a + f + 80 := by
    linarith [h₃]

  rw [h5] at h₁
  rw [h5] at h₂
  
  have eq1 : f = 5 * a - 110 := by
    nlinarith
  
  have eq2 : a = 5 * f - 50 := by
    nlinarith
  
  have ha : a = 25 := by
    linarith [eq1, eq2]
  
  have hf : f = 15 := by
    linarith [eq1, eq2, ha]

  nlinarith [ha, hf]