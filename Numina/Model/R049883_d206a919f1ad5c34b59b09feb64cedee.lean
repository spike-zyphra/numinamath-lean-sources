import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_110397 (f : ℝ → ℝ) :
  (∀ x, f (-x) ≤ x^4 - 2 * x^2 + 3 * x - 1) ↔
  (∀ x, f x ≤ x^4 - 2 * x^2 - 3 * x - 1) := by
  constructor
  · -- Forward direction: Assume ∀ x, f (-x) ≤ x^4 - 2 * x^2 + 3 * x - 1, prove ∀ x, f x ≤ x^4 - 2 * x^2 - 3 * x - 1
    intro h
    intro x
    have h1 := h (-x)
    simp [show (-(-x) : ℝ) = x by ring] at h1
    -- Simplify the right-hand side polynomial to get the desired inequality
    nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x + 1), sq_nonneg (x - 1)]
  · -- Backward direction: Assume ∀ x, f x ≤ x^4 - 2 * x^2 - 3 * x - 1, prove ∀ x, f (-x) ≤ x^4 - 2 * x^2 + 3 * x - 1
    intro h
    intro x
    have h1 := h (-x)
    simp [show (-x : ℝ) = -x by ring] at h1 ⊢
    -- Simplify the right-hand side polynomial to get the desired inequality
    nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x + 1), sq_nonneg (x - 1)]