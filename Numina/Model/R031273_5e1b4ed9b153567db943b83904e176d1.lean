import Mathlib

open Real Set

theorem inequalities_163234 (x : ℝ)(h : x^2 - x - 2 ≥ 0):
    (sqrt (x^2 - x - 2) ≤ 2 * x ↔ x ≥ 2) ∧
    (sqrt (x^2 - x - 2) ≥ 2 * x ↔ x ≤ -1) := by
  constructor
  · -- Forward implication: sqrt (x^2 - x - 2) ≤ 2 * x → x ≥ 2
    constructor
    · -- Forward direction
      intro h1
      by_cases h2 : 2 * x ≥ 0
      · -- If 2 * x ≥ 0, we can square both sides
        have h3 : sqrt (x^2 - x - 2) ≥ 0 := by positivity
        have h4 : 2 * x ≥ 0 := h2
        have h5 : sqrt (x^2 - x - 2) ≤ (2 * x : ℝ) := by linarith
        have h6 : sqrt (x^2 - x - 2) ^ 2 ≤ (2 * x) ^ 2 := by nlinarith [sq_nonneg (sqrt (x^2 - x - 2) - 2 * x), Real.sq_sqrt (show 0 ≤ x^2 - x - 2 by linarith)]
        have h7 : sqrt (x^2 - x - 2) ^ 2 = x^2 - x - 2 := by
          rw [Real.sq_sqrt]
          nlinarith
        nlinarith [show x^2 - x - 2 ≥ 0 by nlinarith]
      · -- Assume 2 * x < 0
        push_neg at h2
        have h3 : sqrt (x^2 - x - 2) ≥ 0 := by positivity
        nlinarith [h2, Real.sqrt_nonneg (x^2 - x - 2)]
    · -- Backward direction
      intro h2
      have h3 : 2 * x ≥ 0 := by nlinarith
      have h4 : sqrt (x^2 - x - 2) ≥ 0 := by positivity
      have h5 : sqrt (x^2 - x - 2) ≤ 2 * x := by
        have h6 : (sqrt (x^2 - x - 2) : ℝ) ^ 2 ≤ (2 * x) ^ 2 := by
          have h7 : (sqrt (x^2 - x - 2) : ℝ) ^ 2 = x^2 - x - 2 := by
            rw [Real.sq_sqrt]
            nlinarith
          nlinarith [show x^2 - x - 2 ≥ 0 by nlinarith, h3]
        have h8 : sqrt (x^2 - x - 2) ≥ 0 := by positivity
        nlinarith [Real.sqrt_nonneg (x^2 - x - 2), h3]
      linarith
  · -- Forward implication: sqrt (x^2 - x - 2) ≥ 2 * x → x ≤ -1
    constructor
    · -- Forward direction
      intro h1
      by_cases h2 : 2 * x ≥ 0
      · -- If 2 * x ≥ 0, we can square both sides
        have h3 : sqrt (x^2 - x - 2) ≥ 0 := by positivity
        have h4 : sqrt (x^2 - x - 2) ≥ (2 * x : ℝ) := by linarith
        have h5 : sqrt (x^2 - x - 2) ^ 2 ≥ (2 * x) ^ 2 := by
          nlinarith [sq_nonneg (sqrt (x^2 - x - 2) - 2 * x), Real.sq_sqrt (show 0 ≤ x^2 - x - 2 by linarith)]
        have h6 : sqrt (x^2 - x - 2) ^ 2 = x^2 - x - 2 := by
          rw [Real.sq_sqrt]
          nlinarith
        nlinarith [h2, show x^2 - x - 2 ≥ 0 by nlinarith]
      · -- Assume 2 * x < 0
        push_neg at h2
        have h3 : sqrt (x^2 - x - 2) ≥ 0 := by positivity
        nlinarith [h2, Real.sqrt_nonneg (x^2 - x - 2)]
    · -- Backward direction
      intro h2
      have h3 : 2 * x ≤ 0 := by linarith
      have h4 : sqrt (x^2 - x - 2) ≥ 0 := by positivity
      have h5 : sqrt (x^2 - x - 2) ≥ (2 * x : ℝ) := by
        linarith [h4, show (2 * x : ℝ) ≤ 0 by linarith, Real.sqrt_nonneg (x^2 - x - 2)]
      linarith