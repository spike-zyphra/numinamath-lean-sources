import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_311966 (p : ℝ) :
  (∀ x : ℝ, x^2 + abs (2 * x - 4) ≥ p) ↔ p ≤ 3 := by
  constructor
  · -- Assume that the inequality x^2 + |2 * x - 4| ≥ p holds for all real x, prove p ≤ 3
    intro h
    have h1 := h 1
    norm_num at h1
    linarith
  · -- Assume p ≤ 3, prove that the inequality x^2 + |2 * x - 4| ≥ p holds for all real x
    intro hp x
    by_cases h : 2 * x - 4 ≥ 0
    · -- Case: 2 * x - 4 ≥ 0, so abs (2 * x - 4) = 2 * x - 4
      have h_abs : abs (2 * x - 4) = 2 * x - 4 := by
        rw [abs_of_nonneg h]
      have h2 : x^2 + abs (2 * x - 4) ≥ 3 := by
        rw [h_abs]
        nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 2)]
      linarith [h2, hp]
    · -- Case: 2 * x - 4 < 0, so abs (2 * x - 4) = -(2 * x - 4)
      have h_abs : abs (2 * x - 4) = -(2 * x - 4) := by
        rw [abs_of_neg (lt_of_not_ge h)]
      have h2 : x^2 + abs (2 * x - 4) ≥ 3 := by
        rw [h_abs]
        nlinarith [sq_nonneg (x - 1)]
      linarith [h2, hp]