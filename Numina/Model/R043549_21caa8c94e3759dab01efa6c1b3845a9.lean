import Mathlib


theorem algebra_184941 : (32 * (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 4) +
    (64 * (1 / 2) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 4) -
    3 * (2 * (2 : ℝ) ^ ((1 : ℝ) / 4)) ^ ((1 : ℝ) / 3) =
    (32 ^ ((1 : ℝ) / 12)) := by

  have h1 : (32 * (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 4) = (2 : ℝ) ^ (17 / 12 : ℝ) := by
    have h2 : (4 : ℝ) ^ ((1 : ℝ) / 3) = (2 : ℝ) ^ (2 / 3 : ℝ) := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals linarith
    have h4 : (32 * (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 4) = (2 : ℝ) ^ (17 / 12 : ℝ) := by
      rw [h2]
      have h5 : (32 * ((2 : ℝ) ^ (2 / 3 : ℝ))) = (2 : ℝ) ^ (17 / 3 : ℝ) := by
        have h6 : (32 : ℝ) = (2 : ℝ) ^ (5 : ℝ) := by norm_num
        rw [h6]
        have h7 : (2 : ℝ) ^ (5 : ℝ) * (2 : ℝ) ^ (2 / 3 : ℝ) = (2 : ℝ) ^ (17 / 3 : ℝ) := by
          rw [← Real.rpow_add]
          norm_num
          all_goals linarith
        linarith
      rw [h5]
      have h8 : ((2 : ℝ) ^ (17 / 3 : ℝ)) ^ ((1 : ℝ) / 4) = (2 : ℝ) ^ (17 / 12 : ℝ) := by
        rw [← Real.rpow_mul]
        ring_nf
        all_goals norm_num
      linarith
    linarith

  have h2 : (64 * (1 / 2 : ℝ) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 4) = (2 : ℝ) ^ (17 / 12 : ℝ) := by
    have h3 : (1 / 2 : ℝ) ^ ((1 : ℝ) / 3) = (2 : ℝ) ^ (-1 / 3 : ℝ) := by
      have h4 : (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) := by norm_num
      rw [h4]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals linarith
    have h4 : (64 * (1 / 2 : ℝ) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 4) = (2 : ℝ) ^ (17 / 12 : ℝ) := by
      rw [h3]
      have h5 : (64 * ((2 : ℝ) ^ (-1 / 3 : ℝ))) = (2 : ℝ) ^ (17 / 3 : ℝ) := by
        have h6 : (64 : ℝ) = (2 : ℝ) ^ (6 : ℝ) := by norm_num
        rw [h6]
        have h7 : (2 : ℝ) ^ (6 : ℝ) * (2 : ℝ) ^ (-1 / 3 : ℝ) = (2 : ℝ) ^ (17 / 3 : ℝ) := by
          rw [← Real.rpow_add]
          norm_num
          all_goals linarith
        linarith
      rw [h5]
      have h8 : ((2 : ℝ) ^ (17 / 3 : ℝ)) ^ ((1 : ℝ) / 4) = (2 : ℝ) ^ (17 / 12 : ℝ) := by
        rw [← Real.rpow_mul]
        ring_nf
        all_goals norm_num
      linarith
    linarith

  have h3 : 3 * (2 * (2 : ℝ) ^ ((1 : ℝ) / 4)) ^ ((1 : ℝ) / 3) = 3 * ((2 : ℝ) ^ (5 / 12 : ℝ)) := by
    have h4 : (2 * (2 : ℝ) ^ ((1 : ℝ) / 4)) ^ ((1 : ℝ) / 3) = (2 : ℝ) ^ (5 / 12 : ℝ) := by
      have h5 : 2 * (2 : ℝ) ^ ((1 : ℝ) / 4) = (2 : ℝ) ^ (5 / 4 : ℝ) := by
        have h6 : (2 : ℝ) ^ (5 / 4 : ℝ) = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (1 / 4 : ℝ) := by
          rw [← Real.rpow_add]
          norm_num
          all_goals linarith
        have h7 : (2 : ℝ) ^ (1 : ℝ) = (2 : ℝ) := by
          simp
        rw [h7] at h6
        linarith
      rw [h5]
      have h8 : ((2 : ℝ) ^ (5 / 4 : ℝ)) ^ ((1 : ℝ) / 3) = (2 : ℝ) ^ (5 / 12 : ℝ) := by
        rw [← Real.rpow_mul]
        ring_nf
        all_goals norm_num
      linarith
    linarith [h4]

  have h4 : (32 ^ ((1 : ℝ) / 12)) = (2 : ℝ) ^ (5 / 12 : ℝ) := by
    have h5 : (32 : ℝ) = (2 : ℝ) ^ (5 : ℝ) := by norm_num
    rw [h5]
    rw [← Real.rpow_mul]
    ring_nf
    all_goals norm_num


  rw [h1, h2, h3, h4]
  have h5 : (2 : ℝ) ^ (17 / 12 : ℝ) = 2 * ((2 : ℝ) ^ (5 / 12 : ℝ)) := by
    have h6 : (2 : ℝ) ^ (17 / 12 : ℝ) = (2 : ℝ) ^ (1 + 5 / 12 : ℝ) := by
      norm_num
    rw [h6]
    have h7 : (2 : ℝ) ^ (1 + 5 / 12 : ℝ) = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (5 / 12 : ℝ) := by
      rw [← Real.rpow_add]
      ring_nf
      all_goals linarith
    have h8 : (2 : ℝ) ^ (1 : ℝ) = (2 : ℝ) := by
      simp
    rw [h7, h8]
    all_goals ring_nf
  linarith [h5]