import Mathlib

theorem algebra_302121 {p q : ℝ} (h : ∃ x : ℝ, x^4 + p * x^2 + q = 0) :
    p^2 ≥ 4 * q ∧ ¬(∀ p q : ℝ, p^2 ≥ 4 * q → ∃ x : ℝ, x^4 + p * x^2 + q = 0) := by
  constructor
  · rcases h with ⟨x, hx⟩
    have h1 : x^2 ≥ 0 := by
      apply sq_nonneg
    have h2 : (x^2)^2 + p*x^2 + q = 0 := by 
      nlinarith
    have h3 : p^2 - 4 * q ≥ 0 := by 
      nlinarith [sq_nonneg (x^2 + p / 2)]
    linarith
  · intro h
    have h1 := h 2 1 (by norm_num)
    rcases h1 with ⟨y, hy⟩
    nlinarith [sq_nonneg (y^2 + 1), sq_nonneg (y^2)]