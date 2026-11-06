import Mathlib

open Real

theorem inequalities_6510 (x : ℝ) :
    (x ^ 2 + 2) / sqrt (x ^ 2 + 1) ≥ 2 ∧
    ((x ^ 2 + 2) / sqrt (x ^ 2 + 1) = 2 ↔ x = 0) := by

  have h1 : (x ^ 2 + 2) / sqrt (x ^ 2 + 1) ≥ 2 := by
    have h2 : sqrt (x ^ 2 + 1) > 0 := by
      apply Real.sqrt_pos.2
      positivity

    have h3 : (x ^ 2 + 2) ≥ 2 * sqrt (x ^ 2 + 1) := by
      nlinarith [sq_nonneg (x ^ 2 - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 + 1 by positivity), sq_nonneg (x ^ 2 + 2 - 2 * sqrt (x ^ 2 + 1)), sq_nonneg (sqrt (x ^ 2 + 1) - 1)]

    have h4 : (x ^ 2 + 2) / sqrt (x ^ 2 + 1) ≥ 2 := by
      have h5 : sqrt (x ^ 2 + 1) > 0 := h2
      apply (le_div_iff₀ h5).mpr
      linarith [h3]

    exact h4
  
  have h5 : (x ^ 2 + 2) / sqrt (x ^ 2 + 1) = 2 ↔ x = 0 := by
    constructor
    · -- Forward implication: if (x^2 + 2) / sqrt(x^2 + 1) = 2, then x = 0
      intro h
      have h2 : sqrt (x ^ 2 + 1) > 0 := by
        apply Real.sqrt_pos.2
        positivity

      have h3 : (x ^ 2 + 2) = 2 * sqrt (x ^ 2 + 1) := by
        field_simp at h ⊢
        nlinarith

      have h4 : (x ^ 2 + 2) ^ 2 = 4 * (x ^ 2 + 1) := by
        calc
          (x ^ 2 + 2) ^ 2 = (2 * sqrt (x ^ 2 + 1)) ^ 2 := by rw [h3]
          _ = 4 * (sqrt (x ^ 2 + 1) ^ 2) := by ring
          _ = 4 * (x ^ 2 + 1) := by rw [Real.sq_sqrt]; positivity

      have h5 : x ^ 4 = 0 := by
        nlinarith

      have h6 : x ^ 2 = 0 := by
        nlinarith [sq_nonneg x]

      have h7 : x = 0 := by
        nlinarith [sq_nonneg x]

      exact h7

    · -- Reverse direction: if x = 0, then (x^2 + 2) / sqrt(x^2 + 1) = 2
      intro h
      rw [h]
      have h2 : sqrt ((0 : ℝ) ^ 2 + 1) = 1 := by
        norm_num [Real.sqrt_eq_iff_sq_eq]
      rw [h2]
      norm_num
  
  constructor
  · exact h1
  · exact h5