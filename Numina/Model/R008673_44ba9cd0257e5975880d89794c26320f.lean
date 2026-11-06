import Mathlib

theorem algebra_9135 (m : ℝ) : (∃ x : ℝ, x^2 + x - 4 * m = 0) ↔ m ≥ -1 / 16 := by
  constructor
  · -- Forward direction: assume there exists a real x satisfying the equation
    intro h
    rcases h with ⟨x, hx⟩
    have h1 : (x + 1 / 2) ^ 2 ≥ 0 := by
      apply sq_nonneg
    nlinarith [sq_nonneg (x + 1 / 2)]
  · -- Backward direction: assume m ≥ -1/16, prove existence of real root
    intro hm
    have h3 : 1 + 16 * m ≥ 0 := by
      linarith
    use (-1 + Real.sqrt (1 + 16 * m)) / 2
    nlinarith [Real.sqrt_nonneg (1 + 16 * m), Real.sq_sqrt (show (1 + 16 * m) ≥ 0 by linarith)]