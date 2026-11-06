import Mathlib

theorem algebra_316567 (b : ℝ) :
    (∀ a : ℝ, ∃ x : ℝ, x^2 - 2 * a * x - a + 2 * b = 0) ↔ b ≤ -1 / 8 := by
  constructor
  · -- Forward: From (∀ a, ∃ x, x^2 - 2*a*x -a + 2 * b = 0) derive b ≤ -1 / 8
    intro h
    have h₁ := h (-1 / 2)
    rcases h₁ with ⟨x, hx⟩
    have h_eq : x^2 + x + (1/2 + 2 * b) = 0 := by
      nlinarith
    nlinarith [sq_nonneg (x + 1 / 2)]
  · -- Backward: From b ≤ -1/8 derive ∀ a, ∃ x, x^2 - 2*a*x -a + 2*b = 0
    intro hb a
    have h1 : (4 * a ^ 2 + 4 * a - 8 * b) ≥ 0 := by
      nlinarith [sq_nonneg (a + 1 / 2), sq_nonneg (b + 1 / 8)]
    use (2 * a + Real.sqrt (4 * a^2 + 4 * a - 8 * b)) / 2
    nlinarith [Real.sqrt_nonneg (4 * a^2 + 4 * a - 8 * b), Real.sq_sqrt (show (4 * a^2 + 4 * a - 8 * b) ≥ 0 by linarith)]