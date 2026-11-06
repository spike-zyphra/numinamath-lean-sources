import Mathlib

theorem inequalities_56811 {g : ℝ → ℝ} (h₁ : ∀ x, g x ≤ x) (h₂ : ∀ x y, g (x + y) ≤ g x + g y) :
    g 1990 = 1990 := by 
  have h3 : g 0 = 0 := by
    have h1 := h₁ 0
    have h2 := h₂ 0 0
    norm_num at h1 h2
    linarith
  have h4 : g 1990 ≤ 1990 := h₁ 1990
  have h5 : g 0 ≤ g (-1990) + g 1990 := by 
    specialize h₂ (-1990) 1990
    norm_num at h₂ ⊢
    linarith
  have h6 : g (-1990) ≤ -1990 := h₁ (-1990)
  rw [h3] at h5
  linarith [h4, h5, h6]