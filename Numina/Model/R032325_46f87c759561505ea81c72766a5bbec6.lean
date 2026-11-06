import Mathlib

theorem algebra_93577 : (4 : ℝ) ^ ((1 : ℝ) / 3) * (8 ^ ((1 : ℝ) / 4)) = 2 * (32 ^ ((1 : ℝ) / 12)) := by

  have h1 : (4 : ℝ) ^ ((1 : ℝ) / 3) = (2 : ℝ) ^ ((2 / 3 : ℝ)) := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num]
    rw [← Real.rpow_mul]
    ring
    all_goals norm_num

  have h2 : (8 : ℝ) ^ ((1 : ℝ) / 4) = (2 : ℝ) ^ ((3 / 4 : ℝ)) := by
    rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) by norm_num]
    rw [← Real.rpow_mul]
    ring
    all_goals norm_num

  have h3 : (2 : ℝ) ^ ((2 / 3 : ℝ)) * ((2 : ℝ) ^ ((3 / 4 : ℝ))) = (2 : ℝ) ^ ((17 / 12 : ℝ)) := by
    rw [← Real.rpow_add]
    norm_num
    all_goals norm_num

  have h4 : (2 : ℝ) ^ ((17 / 12 : ℝ)) = 2 * (32 ^ ((1 : ℝ) / 12)) := by
    have h5 : (32 : ℝ) ^ ((1 : ℝ) / 12) = (2 : ℝ) ^ ((5 / 12 : ℝ)) := by
      rw [show (32 : ℝ) = (2 : ℝ) ^ (5 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring
      all_goals norm_num

    rw [h5]
    have h6 : (2 : ℝ) ^ ((17 / 12 : ℝ)) = 2 * ((2 : ℝ) ^ ((5 / 12 : ℝ))) := by
      have h7 : (2 : ℝ) ^ ((17 / 12 : ℝ)) = (2 : ℝ) ^ ((1 + (5 / 12) : ℝ)) := by
        norm_num

      rw [h7]
      have h8 : (2 : ℝ) ^ ((1 + (5 / 12) : ℝ)) = ((2 : ℝ) ^ ((1 : ℝ))) * ((2 : ℝ) ^ ((5 / 12 : ℝ))) := by
        rw [Real.rpow_add]
        ring_nf
        all_goals norm_num

      rw [h8]
      have h9 : (2 : ℝ) ^ ((1 : ℝ)) = (2 : ℝ) := by
        simp

      rw [h9]
      all_goals norm_num

    linarith

  rw [h1, h2]
  rw [h3, h4]
  all_goals norm_num