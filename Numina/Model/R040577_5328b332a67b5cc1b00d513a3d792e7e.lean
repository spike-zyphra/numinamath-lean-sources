import Mathlib


theorem Inequalities_288589 : ((∀ a b : ℝ, (a < b ∧ a ≠ 0 ∧ b ≠ 0 → 1 / b < 1 / a)) → False) ∧ 
  ((∀ a b c : ℝ, (a < b → a * c < b * c)) → False) ∧ (∀ a b c : ℝ, a < b → a + c < b + c → True) 
  ∧ ((∀ a b : ℝ, (a^2 < b^2 → a < b)) → False) := by
  constructor 
  · -- Show that the first statement is false 
    intro h 
    have h1 := h (-1 : ℝ) (1 : ℝ) ⟨by norm_num, by norm_num, by norm_num⟩ 
    norm_num at h1 
  constructor 
  · -- Show that the second statement is false
    intro h
    have h2 := h (1 : ℝ) (2 : ℝ) (0 : ℝ) (by norm_num)
    norm_num at h2 
  constructor
  · -- Show the third statement is true 
    intro a b c h1 h2 
    trivial 
  · -- Show the fourth statement is false 
    intro h 
    have h3 := h (-1 : ℝ) (-2 : ℝ) 
    norm_num at h3