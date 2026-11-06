import Mathlib

theorem algebra_123720 {f : ℝ → ℝ} (h₁ : ∀ x, f x ≤ x) (h₂ : ∀ x y, f (x + y) ≤ f x + f y) :
    ∀ x, f x = x := by
  have h3 : f 0 = 0 := by
    have h3_1 : f 0 ≤ 0 := h₁ 0
    have h4 : f 0 ≥ 0 := by
      have h5 : f 0 ≤ f 0 + f 0 := by
        specialize h₂ 0 0
        norm_num at h₂ ⊢ 
        linarith 
      linarith 
    linarith 
  intro x 
  have h4 : f x ≥ x := by 
    have h5 : f 0 ≤ f x + f (-x) := by 
      specialize h₂ x (-x)
      norm_num at h₂ ⊢ 
      linarith 
    rw [h3] at h5
    have h6 : f (-x) ≤ -x := h₁ (-x)
    linarith [h5, h6]
  have h7 : f x ≤ x := h₁ x 
  linarith 
  all_goals linarith 
  all_goals linarith 
  <;> nlinarith 
  all_goals try linarith 
  all_goals try linarith 
  all_goals nlinarith 
  all_goals nlinarith 
  all_goals try linarith 
  all_goals try linarith 
  all_goals nlinarith