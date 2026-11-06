import Mathlib

theorem algebra_33 (r : ℝ) : (4 : ℝ) = 2^(5*r + 1) ↔ r = 1 / 5 := by
  constructor
  · -- Assume 4 = 2^(5*r + 1), prove r = 1/5
    intro h
    have h1 : (4 : ℝ) = 2 ^ (5 * r + 1) := by
      linarith
    have h2 : (2 : ℝ) ^ (5 * r + 1 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by
      have h3 : (2 : ℝ) ^ (2 : ℝ) = (4 : ℝ) := by
        norm_num
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by linarith [h3] ] at h1
      linarith
    have h3 : 5 * r + 1 = (2 : ℝ) := by
      apply_fun (Real.logb (2 : ℝ)) at h2
      have h4 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (5 * r + 1 : ℝ)) = 5 * r + 1 := by
        rw [Real.logb_rpow]
        all_goals norm_num
      have h5 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (2 : ℝ)) = (2 : ℝ) := by
        rw [Real.logb_rpow]
        all_goals norm_num
      rw [h4, h5] at h2
      linarith

    have h4 : r = (1 / 5 : ℝ) := by
      linarith
    exact_mod_cast h4
  · -- Assume r = 1/5, prove 4 = 2^(5*r + 1)
    intro h
    rw [h]
    have h1 : (5 * (1 / 5 : ℝ) + 1 : ℝ) = (2 : ℝ) := by
      norm_num
    rw [h1]
    all_goals norm_num