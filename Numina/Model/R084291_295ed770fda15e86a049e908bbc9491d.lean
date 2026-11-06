import Mathlib

theorem algebra_20220 {n d : ℤ} (h₀ : d ≠ 0) (h₁ : (n / d : ℚ) = 5 / 8) (h₂ : n + d = 91) :
    d - n = 21 := by 
  have h3 : (n : ℚ) + (d : ℚ) = 91 := by exact_mod_cast h₂
  have h₃ : (n : ℚ) / (d : ℚ) = (5 / 8 : ℚ) := by exact_mod_cast h₁ 
  have h₄ : (n : ℚ) * 8 = (d : ℚ) * 5 := by 
    have h₅ : (d : ℚ) ≠ 0 := by 
      exact_mod_cast (show d ≠ 0 by exact h₀)
    field_simp [h₅] at h₃ 
    linarith 
    all_goals linarith
  have h₁₁ : (n : ℤ) * 8 = (d : ℤ) * 5 := by 
    have h₁₂ : (n : ℚ) * 8 = (d : ℚ) * 5 := by 
      linarith [h₄]
    exact_mod_cast h₁₂ 
  have eq1 : n = 35 := by 
    nlinarith [h₂, h₁₁]
  have eq2 : d = 56 := by 
    linarith [h₂, eq1] 
  calc 
    d - n = 56 - 35 := by rw [eq2, eq1]
    _ = 21 := by norm_num