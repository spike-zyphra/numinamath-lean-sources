import Mathlib

theorem algebra_107802 (f : ℝ → ℝ) (h₁ : ∀ x, f x ≤ x) (h₂ : ∀ x y, f (x + y) ≤ f x + f y) :
    ∀ x, f x = x := by 
  have h0 : f 0 = 0 := by 
    have h1 := h₂ 0 0 
    norm_num at h1
    have h2 := h₁ 0
    linarith
  intro x
  have h3 := h₂ x (-x)
  have h4 : x + (-x) = (0 : ℝ) := by ring
  rw [h4] at h3 
  rw [h0] at h3 
  have h6 : f (-x) ≤ -x := by 
    have h7 := h₁ (-x)
    linarith 
  have h7 : f x ≥ x := by 
    linarith 
  have h8 : f x ≤ x := h₁ x
  linarith