import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_253702 (x : ℝ) (hx : x^2 - 5 * x + 6 ≠ 0) :
    abs (x - 3) / (x^2 - 5 * x + 6) ≥ 2 ↔ 3 / 2 ≤ x ∧ x < 2 := by
  constructor
  · -- Forward implication: If |x - 3| / (x^2 -5 x +6) >= 2, then 3/2 <= x <2.
    intro h
    have h1 : x^2 - 5 * x + 6 ≠ 0 := hx
    have h3 : x^2 - 5 * x + 6 > 0 ∨ x^2 - 5 * x + 6 < 0 := by
      by_contra h
      push_neg at h
      have : x^2 - 5 * x + 6 = 0 := by linarith
      contradiction
    rcases h3 with h3 | h3
    · -- case where denominator is positive, so x^2 -5 x +6>0.
      have h4 : abs (x - 3) / (x^2 - 5 * x + 6) ≥ 2 := h
      have h5 : abs (x - 3) ≥ 2 * (x^2 - 5 * x + 6) := by
        have h6 : x^2 - 5 * x + 6 > 0 := h3
        apply (le_div_iff₀ h6).mp at h4
        linarith
      by_cases h6 : x ≥ 3
      · -- x ≥ 3.
        rw [abs_of_nonneg (by linarith)] at h5
        nlinarith [sq_nonneg (x - 3), sq_nonneg (x - 2)]
      · -- x < 3.
        rw [abs_of_neg (by linarith)] at h5
        constructor
        · -- Show 3 / 2 ≤ x
          nlinarith [sq_nonneg (x - 3 / 2), sq_nonneg (x - 2), sq_pos_of_ne_zero (show x^2 - 5 * x + 6 ≠ 0 by assumption)]
        · -- Show x < 2
          nlinarith [sq_nonneg (x - 2), sq_nonneg (x - 3 / 2), sq_pos_of_ne_zero (show x^2 - 5 * x + 6 ≠ 0 by assumption)]
    · -- case where denominator is negative, so x^2 -5 x +6 <0.
      have h4 : abs (x - 3) / (x^2 - 5 * x + 6) ≥ 2 := h
      have h7 : abs (x - 3) ≤ 2 * (x^2 - 5 * x + 6) := by
        have h6 : x^2 - 5 * x + 6 < 0 := h3
        apply (le_div_iff_of_neg h6).mp at h4
        linarith
      by_cases h8 : x ≥ 3
      · -- x ≥ 3.
        rw [abs_of_nonneg (by linarith)] at h7
        nlinarith [sq_nonneg (x - 3), sq_nonneg (x - 2)]
      · -- x < 3.
        rw [abs_of_neg (by linarith)] at h7
        nlinarith [sq_nonneg (x - 2), sq_nonneg (x - 3 / 2), sq_pos_of_ne_zero (show x^2 - 5 * x + 6 ≠ 0 by assumption)]
  · -- Backward implication: If 3/2 ≤x <2, then |x -3|/(x^2-5x+6) >=2.
    intro h
    rcases h with ⟨h1, h2⟩
    have h3 : x^2 - 5 * x + 6 > 0 := by nlinarith
    have h4 : abs (x - 3) = 3 - x := by
      rw [abs_of_neg (by linarith)]
      all_goals linarith
    have h5 : abs (x - 3) / (x^2 - 5 * x + 6) ≥ 2 := by
      rw [h4]
      apply (le_div_iff₀ h3).mpr
      nlinarith
    linarith