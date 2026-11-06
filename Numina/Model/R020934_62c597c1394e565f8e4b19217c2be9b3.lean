import Mathlib

theorem algebra_252714 (x : ℝ) : (0.4 : ℝ)^(x - 1) = (6.25 : ℝ)^(6 * x - 5) ↔ x = 11 / 13 := by
  constructor
  · -- Forward direction: if the equation holds, then x = 11/13.
    intro h_eq
    have h1 : (0.4 : ℝ) ^ (x - 1 : ℝ) = (6.25 : ℝ) ^ (6 * x - 5 : ℝ) := h_eq
    have h2 : (6.25 : ℝ) ^ (6 * x - 5 : ℝ) = (0.4 : ℝ) ^ (-2 * (6 * x - 5 : ℝ)) := by
      have h3 : (6.25 : ℝ) = (0.4 : ℝ) ^ (-2 : ℝ) := by norm_num
      rw [h3]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals norm_num
    rw [h2] at h1
    have h3 : x - 1 = -2 * (6 * x - 5) := by
      apply_fun (Real.logb (0.4 : ℝ)) at h1
      have h4 : Real.logb (0.4 : ℝ) ((0.4 : ℝ) ^ (x - 1 : ℝ)) = (x - 1 : ℝ) := by
        rw [Real.logb_rpow]
        all_goals norm_num
      have h5 : Real.logb (0.4 : ℝ) ((0.4 : ℝ) ^ (-2 * (6 * x - 5 : ℝ)) ) = (-2 * (6 * x - 5 : ℝ) ) := by
        rw [Real.logb_rpow]
        all_goals norm_num
      rw [h4, h5] at h1
      linarith
    linarith
  · -- Backward direction: if x = 11/13, then the equation holds.
    intro h_eq
    rw [h_eq]
    have h1 : (0.4 : ℝ) ^ (11 / 13 - 1 : ℝ) = (0.4 : ℝ) ^ (-2 * (6 * (11 / 13 : ℝ) - 5 : ℝ)) := by
      norm_num
    have h2 : (6.25 : ℝ) ^ (6 * (11 / 13 : ℝ) - 5 : ℝ) = (0.4 : ℝ) ^ (-2 * (6 * (11 / 13 : ℝ) - 5 : ℝ)) := by
      have h3 : (6.25 : ℝ) = (0.4 : ℝ) ^ (-2 : ℝ) := by norm_num
      rw [h3]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals norm_num
    rw [h2]
    all_goals norm_num