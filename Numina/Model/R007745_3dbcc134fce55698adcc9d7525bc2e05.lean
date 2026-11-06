import Mathlib

theorem algebra_19644 (a b c : ℕ) (h₀ : (a + b + c) /(3 : ℝ) = 6) (h₁ : c = a + 4)
    (h₂ : b + 4 = (3 / 5 : ℝ) * (a + 4)) :
    c = 10 := by 
  have h₃ : (a + b + c : ℝ) = 18 := by 
    have h₄ : (a + b + c : ℝ) / 3 = 6 := by 
      exact_mod_cast h₀ 
    linarith 
  have h₅ : (c : ℝ) = (a : ℝ) + 4 := by 
    exact_mod_cast h₁ 
  have h₆ : (b : ℝ) = (3 : ℝ) * (a : ℝ) / 5 - 8 / 5 := by 
    have eq1 : (b : ℝ) + 4 = (3 / 5 : ℝ) * (a + 4) := by 
      exact_mod_cast h₂ 
    linarith 
  have h₇ : (a : ℝ) + (b : ℝ) + (c : ℝ) = 18 := by 
    exact_mod_cast h₃ 
  rw [h₅, h₆] at h₇ 
  have ha : (a : ℝ) = 6 := by 
    linarith 
  have hc : (c : ℝ) = 10 := by 
    rw [ha] at h₅ 
    linarith 
  exact_mod_cast hc