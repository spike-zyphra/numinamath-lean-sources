import Mathlib

theorem algebra_96790 (y : ℝ) :
    ¬∃ x : ℝ, x^2 + y^2 + 16 = 0 ∧ x^2 - 3 * y + 12 = 0 := by 
  rintro ⟨x, ⟨h₁, h₂⟩⟩
  have h3 : x^2 ≥ 0 := by apply sq_nonneg
  have h4 : y^2 ≥ 0 := by apply sq_nonneg
  nlinarith