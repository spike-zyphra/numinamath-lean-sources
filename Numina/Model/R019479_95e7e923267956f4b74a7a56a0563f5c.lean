import Mathlib

theorem algebra_96020 (p q : ℝ) (h : ∀ x, x^2 + p * x + q ≥ 0) (h' : ∃ x, x^2 + p * x + q = 0) :
    q = p^2 / 4 := by
  have h1 : q ≥ p^2 / 4 := by
    have h2 := h (-p / 2)
    nlinarith [sq_nonneg (p)]
  have h2 : q ≤ p^2 / 4 := by
    rcases h' with ⟨x, hx_eq⟩
    have h3 : (x + p / 2) ^ 2 ≥ 0 := by
      apply sq_nonneg
    nlinarith [h3]
  linarith