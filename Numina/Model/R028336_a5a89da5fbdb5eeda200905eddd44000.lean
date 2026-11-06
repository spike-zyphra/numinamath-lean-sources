import Mathlib

theorem algebra_317138 (c d a b : ℝ × ℝ)
    (h₀ : c ≠ 0) (h₁ : d ≠ 0)
    (h₂ : ¬Collinear ℝ {c, d}) :
    ¬Collinear ℝ {a, b} ↔ a = c + d ∧ b = 2 * c - 2 * d := by
  have h3 : False := h₂ (by
    apply collinear_pair
  )
  exfalso
  tauto