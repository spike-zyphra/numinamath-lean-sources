import Mathlib

theorem number_theory_248894 : (729 ^ ((1 : ℝ) / 3)) < Real.sqrt 121 ∧ Real.sqrt 121 < (38416 ^ ((1 : ℝ) / 4)) := by
  have h1 : (729 : ℝ) ^ ((1 : ℝ) / 3) = (9 : ℝ) := by
    have h2 : (729 : ℝ) = (9 : ℝ) ^ (3 : ℝ) := by norm_num
    rw [h2]
    have h3 : ((9 : ℝ) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) = (9 : ℝ) := by
      rw [← Real.rpow_mul]
      norm_num
      all_goals norm_num
    linarith
  have h4 : Real.sqrt (121 : ℝ) = (11 : ℝ) := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h5 : (38416 : ℝ) ^ ((1 : ℝ) / 4) = (14 : ℝ) := by
    have h6 : (38416 : ℝ) = (14 : ℝ) ^ (4 : ℝ) := by norm_num
    rw [h6]
    have h7 : ((14 : ℝ) ^ (4 : ℝ)) ^ ((1 : ℝ) / 4) = (14 : ℝ) := by
      rw [← Real.rpow_mul]
      norm_num
      all_goals norm_num
    linarith
  rw [h1, h4]
  constructor
  · norm_num
  · -- Prove the second inequality
    rw [h5]
    all_goals norm_num