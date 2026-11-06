import Mathlib

theorem inequalities_607249 (x : ℝ) (hx : 0 ≤ x) : 1 + x^2 + x^6 + x^8 ≥ 4 * x^4 ∧
(1 + x^2 + x^6 + x^8 = 4 * x^4 ↔ x = 1) := by 
  constructor
  · -- Prove the inequality
    nlinarith [sq_nonneg (x^4 - 1), sq_nonneg (x^2 - 1), sq_nonneg (x^2 - x^4), sq_nonneg (x^3 - x), sq_nonneg (x^4 - x^2), sq_nonneg (x^2 - 1), mul_nonneg hx hx, sq_nonneg (x^2 - x^4)]
  · -- Prove the equality condition
    constructor
    · -- Forward implication: Equality implies x = 1
      intro heq
      have h1 : (x - 1) ^ 2 = 0 := by
        nlinarith [sq_nonneg (x^4 - 1), sq_nonneg (x^2 - 1), sq_nonneg (x^2 - x^4), sq_nonneg (x^3 - x), sq_nonneg (x^4 - x^2), sq_nonneg (x^2 - 1), mul_nonneg hx hx, sq_nonneg (x^2 - x^4)]
      have h2 : x - 1 = 0 := by
        rw [sq_eq_zero_iff] at h1
        exact h1
      linarith
    · -- Backward implication: x = 1 implies equality
      intro heq
      rw [show x = 1 by linarith [heq]]
      norm_num