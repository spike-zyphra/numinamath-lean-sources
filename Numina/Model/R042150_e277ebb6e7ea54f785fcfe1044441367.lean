import Mathlib

theorem algebra_4812 (x : ℝ) : (3 : ℝ) ^ x = (-27) ^ (-6 : ℝ) ↔ x = -18 := by
  constructor
  · -- Assume (3 : ℝ) ^ x = (-27) ^ (-6 : ℝ), prove x = -18
    intro h_eq
    have h1 : (-27 : ℝ) ^ (-6 : ℝ) = (3 : ℝ) ^ (-18 : ℝ) := by
      norm_num
    rw [h1] at h_eq
    have h2 : x = (-18 : ℝ) := by
      apply_fun (Real.logb (3 : ℝ)) at h_eq
      have h3 : Real.logb (3 : ℝ) ((3 : ℝ) ^ x) = x := by 
        rw [Real.logb_rpow]
        all_goals norm_num
      have h4 : Real.logb (3 : ℝ) ((3 : ℝ) ^ (-18 : ℝ)) = (-18 : ℝ) := by
        rw [Real.logb_rpow]
        all_goals norm_num
      rw [h3, h4] at h_eq
      linarith
    exact h2
  · -- Assume x = -18, prove (3 : ℝ) ^ x = (-27) ^ (-6 : ℝ)
    intro h_eq
    rw [h_eq]
    norm_num