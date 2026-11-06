import Mathlib

open Real Set

theorem inequalities_310527 (a : ℝ) :
    (∀ x : ℝ, x^2 + abs (2 * x - 6) ≥ a) ↔ a ≤ 5 := by
  constructor
  · -- Assume $ ∀ x : ℝ, x^2 + abs (2 * x - 6) ≥ a $, we need to prove $a ≤ 5$
    intro h
    have h1 := h 1
    norm_num at h1
    linarith
  · -- Assume a ≤ 5, we need to show ∀ x : ℝ, x^2 + abs (2 * x - 6) ≥ a
    intro ha x
    have h1 : x ^ 2 + abs (2 * x - 6) ≥ 5 := by
      by_cases h : 2 * x - 6 ≥ 0
      · -- case where 2x - 6 ≥ 0, i.e., x ≥ 3
        rw [abs_of_nonneg h]
        nlinarith [sq_nonneg (x - 3), sq_nonneg (x + 1)]
      · -- case where 2x - 6 < 0, i.e., x < 3
        rw [abs_of_neg (lt_of_not_ge h)]
        nlinarith [sq_nonneg (x - 1)]
    linarith [h1, ha]