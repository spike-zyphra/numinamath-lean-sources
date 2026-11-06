import Mathlib

theorem algebra_10837 {A B C D : ℤ} (h₀ : A > 0) (h₁ : B > 0) (h₂ : C > 0) (h₃ : D > 0)
    (h₄ : A + B + C + D = 36) (h₅ : A + 2 = B - 2) (h₆ : B - 2 = C * 2) (h₇ : C * 2 = (D / 2:ℚ)) :
    A * B * C * D = 3840 := by

  have h₈ : (D : ℚ) = 4 * (C : ℚ) := by 
    linarith
  
  have h₉ : D = 4 * C := by 
    exact_mod_cast h₈
  
  have h₁₀ : A = 2 * C - 2 := by 
    linarith [h₅, h₆]

  have h₁₁ : B = 2 * C + 2 := by 
    linarith [h₆]

  rw [h₁₀, h₁₁, h₉] at h₄

  have h₁₂ : C = 4 := by
    linarith
  
  have h₁₃ : A = 6 := by 
    linarith [h₁₂, h₁₀]

  have h₁₄ : B = 10 := by 
    linarith [h₁₂, h₁₁]

  have h₁₅ : D = 16 := by 
    linarith [h₁₂, h₉]

  rw [h₁₃, h₁₄, h₁₂, h₁₅]
  all_goals norm_num