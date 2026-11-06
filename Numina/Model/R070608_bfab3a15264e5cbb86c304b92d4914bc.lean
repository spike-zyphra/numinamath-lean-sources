import Mathlib

open Real

theorem inequalities_224496 (a : ℝ) :
    (∀ x : ℝ, 2 * x ^ 2 - a * sqrt (x ^ 2 + 1) + 3 ≥ 0) ↔ a ≤ 3 := by
  constructor
  · -- Forward implication: If the inequality holds for all x, then a ≤ 3.
    intro h
    have h1 := h 0
    have h4 : sqrt (0 ^ 2 + 1) = 1 := by
      norm_num [sqrt_eq_iff_sq_eq]
    rw [h4] at h1
    linarith

  · -- Reverse implication: If a ≤ 3, then the inequality holds for all x.
    intro ha x
    have h1 : sqrt (x ^ 2 + 1) ≥ 0 := by
      apply sqrt_nonneg
    have h2 : sqrt (x ^ 2 + 1) ≥ 1 := by
      have h3 : x ^ 2 ≥ 0 := sq_nonneg x
      have h4 : (x ^ 2 + 1 : ℝ) ≥ 1 := by
        linarith
      have h5 : sqrt (x ^ 2 + 1) ≥ sqrt (1 : ℝ) := by
        apply Real.sqrt_le_sqrt
        linarith
      have h6 : sqrt (1 : ℝ) = 1 := Real.sqrt_one
      linarith
    nlinarith [sq_nonneg (x ^ 2 - 3 / 4), Real.sqrt_nonneg (x ^ 2 + 1),
      Real.sq_sqrt (show x ^ 2 + 1 ≥ 0 by positivity), sq_nonneg (sqrt (x ^ 2 + 1) - 3 / 2), sq_nonneg (sqrt (x ^ 2 + 1) - 1), sq_nonneg (x), ha
      ]