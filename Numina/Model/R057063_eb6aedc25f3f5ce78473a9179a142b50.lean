import Mathlib

theorem algebra_21105 (r : ℝ) : (5 : ℝ)^(2*r-3) = 25 ↔ r = 5 / 2 := by
  constructor
  · -- Assume (5 : ℝ) ^ (2 * r - 3) = 25, prove r = 5 / 2
    intro h
    have h1 : (5 : ℝ) ^ (2 * r - 3) = 25 := h
    have h2 : 2 * r - 3 = (2 : ℝ) := by
      have h3 : (5 : ℝ) ^ (2 * r - 3) = 25 := h1
      have h4 : (25 : ℝ) = (5 : ℝ) ^ (2 : ℝ) := by norm_num
      rw [h4] at h3
      have h5 : (2 * r - 3 : ℝ) = (2 : ℝ) := by
        apply_fun (Real.logb 5) at h3
        have h6 : Real.logb 5 ((5 : ℝ) ^ (2 * r - 3 : ℝ)) = (2 * r - 3 : ℝ) := by
          rw [Real.logb_rpow]
          all_goals norm_num
        have h7 : Real.logb 5 ((5 : ℝ) ^ (2 : ℝ)) = (2 : ℝ) := by
          rw [Real.logb_rpow]
          all_goals norm_num
        rw [h6, h7] at h3
        linarith
      linarith
    have h3 : r = 5 / 2 := by linarith
    exact h3
  · -- Assume r = 5/2, prove (5 : ℝ)^(2*r-3) = 25
    intro h
    rw [h]
    norm_num [Real.rpow_mul, Real.rpow_sub]
    all_goals norm_num
    all_goals norm_num [Real.rpow_natCast, Real.rpow_mul, Real.rpow_sub]
    all_goals norm_num