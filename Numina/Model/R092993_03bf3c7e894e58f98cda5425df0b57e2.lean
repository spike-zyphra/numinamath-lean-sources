import Mathlib

theorem algebra_259686 (d : ℝ) (h₀ : d > 0) (h₁ : (d / 2) / (31 + 1 / 5) = (d / 2) / (26 + 1 / 4) + 2 / d) :
    d = 58 := by
  field_simp at h₁ ⊢
  nlinarith [h₀]