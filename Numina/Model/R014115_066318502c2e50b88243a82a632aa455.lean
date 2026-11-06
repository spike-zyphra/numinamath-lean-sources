import Mathlib

theorem algebra_153420 : ((9 / 16 : ℝ) ^ (-1 / 10 : ℝ) / ((25 / 36) ^ (-3 / 2 : ℝ))) -
    ((4 / 3) ^ (-1 / 2 : ℝ)) ^ (-2 / 5 : ℝ) * (6 / 5) ^ (-3 : ℝ) = 0 := by

  have h1 : ((9 / 16 : ℝ) ^ (-1 / 10 : ℝ) ) = ((4 / 3) ^ (1 / 5 : ℝ)) := by
    have h2 : (9 / 16 : ℝ) = (3 / 4) ^ (2 : ℝ) := by norm_num
    rw [h2]
    have h3 : ((3 / 4 : ℝ) ^ (2 : ℝ)) ^ (-1 / 10 : ℝ) = (3 / 4) ^ (2 * (-1 / 10) : ℝ) := by
      rw [← Real.rpow_mul]
      ring_nf
      all_goals norm_num
    have h4 : (3 / 4 : ℝ) ^ (2 * (-1 / 10) : ℝ) = (3 / 4 : ℝ) ^ (-1 / 5 : ℝ) := by
      norm_num
    have h5 : (3 / 4 : ℝ) ^ (-1 / 5 : ℝ) = ((4 / 3) ^ (1 / 5 : ℝ)) := by
      have h11 : (3 / 4 : ℝ) ^ (-1 / 5 : ℝ) = ((4 / 3) ^ (1 / 5 : ℝ)) := by
        rw [show (4 / 3 : ℝ) = (3 / 4) ^ (-1 : ℝ) by norm_num]
        rw [← Real.rpow_mul]
        norm_num
        all_goals norm_num
      linarith [h11]
    rw [h3, h4, h5]

  have h2 : ((25 / 36 : ℝ) ^ (-3 / 2 : ℝ)) = ((6 / 5) ^ (3 : ℝ)) := by
    have h3 : (25 / 36 : ℝ) = (5 / 6) ^ (2 : ℝ) := by norm_num
    rw [h3]
    have h4 : ((5 / 6 : ℝ) ^ (2 : ℝ)) ^ (-3 / 2 : ℝ) = (5 / 6) ^ (2 * (-3 / 2) : ℝ) := by
      rw [← Real.rpow_mul]
      ring_nf
      all_goals norm_num
    have h5 : (5 / 6 : ℝ) ^ (2 * (-3 / 2) : ℝ) = (5 / 6) ^ (-3 : ℝ) := by
      norm_num
    have h6 : (5 / 6 : ℝ) ^ (-3 : ℝ) = ((6 / 5) ^ (3 : ℝ)) := by
      have h7 : (5 / 6 : ℝ) ^ (-3 : ℝ) = ((6 / 5) ^ (3 : ℝ)) := by
        rw [show (6 / 5 : ℝ) = (5 / 6) ^ (-1 : ℝ) by norm_num]
        rw [← Real.rpow_mul]
        norm_num
        all_goals norm_num
      linarith [h7]
    rw [h4, h5, h6]

  have h3 : ( ((4 / 3 : ℝ) ^ (-1 / 2 : ℝ)) ^ (-2 / 5 : ℝ) ) = ((4 / 3) ^ (1 / 5 : ℝ)) := by
    rw [← Real.rpow_mul]
    norm_num
    all_goals norm_num

  have h4 : ((6 / 5 : ℝ) ^ (-3 : ℝ)) = ((5 / 6) ^ (3 : ℝ)) := by
    have h5 : (6 / 5 : ℝ) ^ (-3 : ℝ) = (5 / 6) ^ (3 : ℝ) := by
      rw [show (5 / 6 : ℝ) = (6 / 5) ^ (-1 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      norm_num
      all_goals norm_num
    linarith [h5]

  rw [h1, h2, h3, h4]
  field_simp
  <;> ring_nf
  <;> norm_num