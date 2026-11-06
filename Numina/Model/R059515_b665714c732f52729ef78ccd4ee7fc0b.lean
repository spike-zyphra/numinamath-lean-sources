import Mathlib

theorem inequalities_2105
    (a b : ℝ)
    (h₀ : a < b)
    (h₁ : b < 0) : a / b > 1 := by 
  have h₂ : a < 0 := by linarith
  have h₃ : a - b < 0 := by linarith 
  have h₄ : (a - b) / b > 0 := by 
    apply div_pos_of_neg_of_neg
    linarith
    linarith 
  have h₅ : a / b - 1 > 0 := by 
    have h₆ : a / b - 1 = (a - b) / b := by 
      field_simp [(show b ≠ 0 by linarith)]
      <;> ring 
    rw [h₆]
    all_goals linarith [h₄]
  linarith [h₅]