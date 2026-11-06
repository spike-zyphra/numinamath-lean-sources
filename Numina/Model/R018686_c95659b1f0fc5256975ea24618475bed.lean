import Mathlib

theorem inequalities_254056 (x : ℝ) : (25 : ℝ) ^ x > 125 ^ (3 * x - 2) ↔ x < 6 / 7 := by
  constructor
  · -- Assume $25^x > 125^{3x-2}$, prove $x < 6/7$
    intro h
    have h25 : (25 : ℝ) ^ x = (5 : ℝ) ^ (2 * x) := by
      rw [show (25 : ℝ) = (5 : ℝ) ^ (2 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals norm_num
    have h125 : (125 : ℝ) ^ (3 * x - 2 : ℝ) = (5 : ℝ) ^ (9 * x - 6 : ℝ) := by
      rw [show (125 : ℝ) = (5 : ℝ) ^ (3 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals norm_num
    rw [h25, h125] at h
    have h4 : x < (6 / 7 : ℝ) := by
      by_contra h4
      push_neg at h4
      have h7 : x ≥ (6 / 7 : ℝ) := by linarith
      have h5 : (2 * x) ≤ (9 * x - 6 : ℝ) := by
        linarith
      have h5_pow : (5 : ℝ) ^ (2 * x : ℝ) ≤ (5 : ℝ) ^ (9 * x - 6 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le
        all_goals norm_num
        all_goals linarith
      linarith
    linarith [h4]
  · -- Assume x < 6/7, prove $25^x > 125^{3x-2}$
    intro h
    have h25 : (25 : ℝ) ^ x = (5 : ℝ) ^ (2 * x) := by
      rw [show (25 : ℝ) = (5 : ℝ) ^ (2 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals norm_num
    have h125 : (125 : ℝ) ^ (3 * x - 2 : ℝ) = (5 : ℝ) ^ (9 * x - 6 : ℝ) := by
      rw [show (125 : ℝ) = (5 : ℝ) ^ (3 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals norm_num
    rw [h25, h125]
    have h7 : (2 * x) > (9 * x - 6 : ℝ) := by
      linarith
    have h5_pow : (5 : ℝ) ^ (2 * x : ℝ) > (5 : ℝ) ^ (9 * x - 6 : ℝ) := by
      apply Real.rpow_lt_rpow_of_exponent_lt
      all_goals norm_num
      all_goals linarith
    linarith [h5_pow]