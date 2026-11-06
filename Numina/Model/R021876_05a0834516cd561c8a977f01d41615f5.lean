import Mathlib


theorem algebra_198094 (c : ℝ) (hc : c = 2 * Real.sqrt 3 * (1.5) ^ ((1 : ℝ) / 3) * (12) ^ ((1 : ℝ) / 6)) : c = 6 := by
  have h1 : Real.sqrt 3 = (3 : ℝ) ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
  have h2 : (1.5 : ℝ) = (3 / 2 : ℝ) := by norm_num
  have h3 : (12 : ℝ) ^ (1 / 6 : ℝ) = (2 : ℝ) ^ (1 / 3 : ℝ) * (3 : ℝ) ^ (1 / 6 : ℝ) := by
    have h4 : (12 : ℝ) ^ (1 / 6 : ℝ) = ((2 : ℝ) ^ (2 : ℝ) * (3 : ℝ)) ^ (1 / 6 : ℝ) := by
      norm_num
    rw [h4]
    have h5 : ((2 : ℝ) ^ (2 : ℝ) * (3 : ℝ)) ^ (1 / 6 : ℝ) =
        ((2 : ℝ) ^ (2 : ℝ)) ^ (1 / 6 : ℝ) * (3 : ℝ) ^ (1 / 6 : ℝ) := by
      rw [← Real.mul_rpow]
      all_goals norm_num
    rw [h5]
    have h6 : ((2 : ℝ) ^ (2 : ℝ)) ^ (1 / 6 : ℝ) = (2 : ℝ) ^ (1 / 3 : ℝ) := by
      rw [← Real.rpow_mul]
      ring_nf
      all_goals norm_num
    rw [h6]
  have h7 : (3 / 2 : ℝ) ^ (1 / 3 : ℝ) = (3 : ℝ) ^ (1 / 3 : ℝ) * (2 : ℝ) ^ (-1 / 3 : ℝ) := by
    have h8 : (3 / 2 : ℝ) ^ (1 / 3 : ℝ) = (3 : ℝ) ^ (1 / 3 : ℝ) / (2 : ℝ) ^ (1 / 3 : ℝ) := by
      rw [show (3 / 2 : ℝ) = (3 : ℝ) / (2 : ℝ) by norm_num]
      rw [← Real.div_rpow]
      all_goals norm_num
    rw [h8]
    have h10 : (3 : ℝ) ^ (1 / 3 : ℝ) / (2 : ℝ) ^ (1 / 3 : ℝ) = (3 : ℝ) ^ (1 / 3 : ℝ) * (2 : ℝ) ^ (-1 / 3 : ℝ) := by
      have h11 : (2 : ℝ) ^ (-1 / 3 : ℝ) = 1 / ((2 : ℝ) ^ (1 / 3 : ℝ)) := by
        have h12 : (2 : ℝ) ^ (-1 / 3 : ℝ) = ((2 : ℝ) ^ (1 / 3 : ℝ))⁻¹ := by
          rw [← Real.rpow_neg]
          ring_nf
          all_goals norm_num
        rw [h12]
        field_simp
      rw [h11]
      field_simp
    rw [h10]
  rw [hc, h1, h2, h3, h7]
  have h8 : 2 * ((3 : ℝ) ^ (1 / 2 : ℝ) ) * ((3 : ℝ) ^ (1 / 3 : ℝ) * (2 : ℝ) ^ (-1 / 3 : ℝ)) * ((2 : ℝ) ^ (1 / 3 : ℝ) * (3 : ℝ) ^ (1 / 6 : ℝ)) = 6 := by
    have h9 : 2 * ((3 : ℝ) ^ (1 / 2 : ℝ) ) * ((3 : ℝ) ^ (1 / 3 : ℝ) * (2 : ℝ) ^ (-1 / 3 : ℝ)) * ((2 : ℝ) ^ (1 / 3 : ℝ) * (3 : ℝ) ^ (1 / 6 : ℝ)) =
        (3 : ℝ) ^ (1 / 2 + 1 / 3 + 1 / 6 : ℝ) * (2 : ℝ) ^ (1 + (-1 / 3 : ℝ) + (1 / 3 : ℝ)) := by
      have h10 : 2 * ((3 : ℝ) ^ (1 / 2 : ℝ) ) * ((3 : ℝ) ^ (1 / 3 : ℝ) * (2 : ℝ) ^ (-1 / 3 : ℝ)) * ((2 : ℝ) ^ (1 / 3 : ℝ) * (3 : ℝ) ^ (1 / 6 : ℝ)) =
          (3 : ℝ) ^ (1 / 2 : ℝ) * (3 : ℝ) ^ (1 / 3 : ℝ) * (3 : ℝ) ^ (1 / 6 : ℝ) * (2 * (2 : ℝ) ^ (-1 / 3 : ℝ) * (2 : ℝ) ^ (1 / 3 : ℝ)) := by
        ring_nf
      rw [h10]
      have h11 : (3 : ℝ) ^ (1 / 2 : ℝ) * (3 : ℝ) ^ (1 / 3 : ℝ) * (3 : ℝ) ^ (1 / 6 : ℝ) = (3 : ℝ) ^ (1 / 2 + 1 / 3 + 1 / 6 : ℝ) := by
        rw [← Real.rpow_add, ← Real.rpow_add]
        all_goals norm_num
      have h12 : 2 * (2 : ℝ) ^ (-1 / 3 : ℝ) * (2 : ℝ) ^ (1 / 3 : ℝ) = (2 : ℝ) ^ (1 + (-1 / 3 : ℝ) + (1 / 3 : ℝ)) := by
        have h121 : 2 * (2 : ℝ) ^ (-1 / 3 : ℝ) * (2 : ℝ) ^ (1 / 3 : ℝ) = (2 : ℝ) ^ (1 : ℝ) * ((2 : ℝ) ^ (-1 / 3 : ℝ) * (2 : ℝ) ^ (1 / 3 : ℝ)) := by
          ring_nf
        rw [h121]
        have h122 : (2 : ℝ) ^ (1 : ℝ) = (2 : ℝ) := by
          norm_num
        rw [h122]
        have h123 : (2 : ℝ) ^ (-1 / 3 : ℝ) * (2 : ℝ) ^ (1 / 3 : ℝ) = (2 : ℝ) ^ (-1 / 3 + 1 / 3 : ℝ) := by
          rw [← Real.rpow_add]
          ring_nf
          all_goals norm_num
        rw [h123]
        have h124 : (-1 / 3 + 1 / 3 : ℝ) = (0 : ℝ) := by
          norm_num
        rw [h124]
        have h125 : (2 : ℝ) ^ (0 : ℝ) = 1 := by
          norm_num
        simp [h125]
        all_goals norm_num
      rw [h11, h12]
    rw [h9]
    have h10 : (3 : ℝ) ^ (1 / 2 + 1 / 3 + 1 / 6 : ℝ) * (2 : ℝ) ^ (1 + (-1 / 3 : ℝ) + (1 / 3 : ℝ)) = 6 := by
      have h11 : (3 : ℝ) ^ (1 / 2 + 1 / 3 + 1 / 6 : ℝ) = 3 := by
        have h12 : (1 / 2 + 1 / 3 + 1 / 6 : ℝ) = (1 : ℝ) := by
          norm_num
        rw [h12]
        all_goals norm_num
      have h13 : (2 : ℝ) ^ (1 + (-1 / 3 : ℝ) + (1 / 3 : ℝ)) = 2 := by
        have h14 : (1 + (-1 / 3 : ℝ) + (1 / 3 : ℝ)) = (1 : ℝ) := by
          norm_num
        rw [h14]
        all_goals norm_num
      rw [h11, h13]
      all_goals norm_num
    linarith
  linarith [h8]