import Mathlib

theorem algebra_8098 (m : ℝ) :
    (∀ x : ℝ, -x^2 + 3 * x + m ≠ 0) ↔ m < -9 / 4 := by
  constructor
  · -- Assume that for all real numbers x, -x^2 + 3 * x + m ≠ 0, prove that m < -9 / 4
    intro h
    by_contra h1
    push_neg at h1
    have h2 : m ≥ -9 / 4 := by linarith
    have h3 : ∃ x : ℝ, -x ^ 2 + 3 * x + m = 0 := by
      have h4 : 9 + 4 * m ≥ 0 := by linarith
      use (3 + Real.sqrt (9 + 4 * m)) / 2
      nlinarith [Real.sqrt_nonneg (9 + 4 * m), Real.sq_sqrt (show (0 : ℝ) ≤ 9 + 4 * m by linarith)]
    rcases h3 with ⟨x, hx⟩
    have h4 : -x ^ 2 + 3 * x + m ≠ 0 := h x
    contradiction
  · -- Assume m < -9 / 4, prove that ∀ x : ℝ, -x^2 + 3 * x + m ≠ 0
    intro h x
    by_contra h1
    have h2 : -x^2 + 3 * x + m = 0 := by linarith
    have h3 : m ≥ -9 / 4 := by
      nlinarith [sq_nonneg (x - 3 / 2)]
    linarith