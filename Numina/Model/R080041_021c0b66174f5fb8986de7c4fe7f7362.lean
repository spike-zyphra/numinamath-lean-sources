import Mathlib

open Real

theorem algebra_252563 (x : ℝ) (hx : x^2 - 4 * x + 6 > 0) :
    x^2 + 3 + logb 2 (x^2 - 4 * x + 6) = 4 * x ↔ x = 2 := by
  constructor
  · -- Forward direction: if the equation holds, then x = 2
    intro h_eq
    have h1 : x^2 - 4 * x + 6 = (x - 2)^2 + 2 := by
      ring
    have h2 : logb 2 (x^2 - 4 * x + 6) = logb 2 ((x - 2)^2 + 2) := by
      rw [h1]
    have h3 : logb 2 ((x - 2)^2 + 2) ≥ 1 := by
      have h4 : (x - 2)^2 + 2 ≥ (2 : ℝ) := by
        nlinarith [sq_nonneg (x - 2)]
      have h5 : logb 2 ((x - 2)^2 + 2) ≥ logb 2 (2 : ℝ) := by
        apply Real.logb_le_logb_of_le
        all_goals nlinarith
      have h6 : logb 2 (2 : ℝ) = 1 := by
        norm_num [Real.logb_self_eq_one]
      linarith
    have h4 : x^2 + 3 + logb 2 (x^2 - 4 * x + 6) ≥ x^2 + 3 + 1 := by
      have h5 : logb 2 (x^2 - 4 * x + 6) ≥ 1 := by
        rw [h2]
        linarith [h3]
      linarith
    have h5 : x^2 + 3 + logb 2 (x^2 - 4 * x + 6) ≥ x^2 + 4 := by
      linarith [h4]
    have h6 : 4 * x ≥ x^2 + 4 := by linarith [h_eq, h5]
    have h7 : (x - 2)^2 ≤ 0 := by
      nlinarith
    have h8 : x - 2 = 0 := by
      nlinarith [sq_nonneg (x - 2)]
    linarith
  · -- Backward direction: if x = 2, then the equation holds
    intro h_eq
    rw [h_eq]
    have h1 : (2 : ℝ)^2 - 4 * (2 : ℝ) + 6 = (2 : ℝ) := by
      norm_num
    have h2 : logb 2 ((2 : ℝ)^2 - 4 * (2 : ℝ) + 6) = 1 := by
      rw [h1]
      norm_num [Real.logb_eq_iff_rpow_eq]
    norm_num [h2]
    all_goals norm_num