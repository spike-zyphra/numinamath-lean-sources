import Mathlib

theorem algebra_161702 {a b c : ℝ} (h₀ : a + b + c = 0) (h₁ : a * b * c = 8) :
    1 / a + 1 / b + 1 / c < 0 := by
  have h2 : a ≠ 0 := by 
    by_contra h 
    have h3 : a = 0 := by linarith
    rw [h3] at h₁ 
    nlinarith
  have h3 : b ≠ 0 := by 
    by_contra h 
    have h4 : b = 0 := by linarith
    rw [h4] at h₁ 
    nlinarith 
  have h4 : c ≠ 0 := by
    by_contra h 
    have h5 : c = 0 := by linarith
    rw [h5] at h₁ 
    nlinarith
  have h5 : 1 / a + 1 / b + 1 / c = (a * b + a * c + b * c) / (a * b * c) := by 
    field_simp [h2, h3, h4]
    ring 
  have h6 : a * b + a * c + b * c < 0 := by 
    have h7 : a^2 + b^2 + c^2 > 0 := by
      nlinarith [sq_nonneg (a * b), sq_nonneg (b * c), sq_nonneg (c * a), 
          sq_pos_of_ne_zero (show a ≠ 0 by assumption), sq_pos_of_ne_zero (show b ≠ 0 by assumption), sq_pos_of_ne_zero (show c ≠ 0 by assumption)
        ]
    have h8 : (a + b + c) ^ 2 = a^2 + b^2 + c^2 + 2 * (a * b + a * c + b * c) := by 
      ring 
    rw [h₀] at h8
    nlinarith 
  rw [h5] 
  have h8 : (a * b + a * c + b * c) / (a * b * c) < 0 := by 
    apply div_neg_of_neg_of_pos 
    · exact h6 
    · -- Show the product is positive 
      nlinarith [h₁]
  linarith