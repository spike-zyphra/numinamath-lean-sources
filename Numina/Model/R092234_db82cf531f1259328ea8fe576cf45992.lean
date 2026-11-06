import Mathlib

theorem algebra_3056
    (a b c1 c2 c3 : ℝ)
    (h₀ : a ≠ 0)
    (h₁ : b ≠ 0)
    (h₂ : (c2 - c1) / a = (c3 - c2) / a) :
    2 * c2 = c1 + c3 := by 
  have h3 : c2 - c1 = c3 - c2 := by 
    have h4 : a ≠ 0 := h₀
    field_simp [h4] at h₂ 
    linarith
  linarith