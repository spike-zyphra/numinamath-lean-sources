import Mathlib

theorem algebra_185133 : 4 / (13 ^ ((1 : ℝ) / 4) - 9 ^ ((1 : ℝ) / 4)) = (13 ^ ((1 : ℝ) / 4) + 9 ^ ((1 : ℝ) / 4)) * (Real.sqrt 13 + 3) := by
  have h1 : (13 : ℝ) ^ ((1 : ℝ) / 4) > 0 := by positivity
  have h2 : (9 : ℝ) ^ ((1 : ℝ) / 4) > 0 := by positivity
  have h3 : (13 : ℝ) ^ ((1 : ℝ) / 4) - (9 : ℝ) ^ ((1 : ℝ) / 4) ≠ 0 := by
    by_contra h
    have h4 : (13 : ℝ) ^ ((1 : ℝ) / 4) = (9 : ℝ) ^ ((1 : ℝ) / 4) := by linarith
    have h5 : ( (13 : ℝ) ^ ((1 : ℝ) / 4) ) ^ 4 = ( (9 : ℝ) ^ ((1 : ℝ) / 4) ) ^ 4 := by rw [h4]
    have h6 : ( (13 : ℝ) ^ ((1 : ℝ) / 4) ) ^ 4 = (13 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals positivity
    have h7 : ( (9 : ℝ) ^ ((1 : ℝ) / 4) ) ^ 4 = (9 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals positivity
    rw [h6, h7] at h5
    all_goals linarith
  have h6 : ( (13 : ℝ ) ^ ((1 : ℝ) / 4) ) ^ 2 = Real.sqrt 13 := by
    have h61 : ( (13 : ℝ ) ^ ((1 : ℝ) / 4) ) ^ 2 = (13) ^ (1 / 2 : ℝ ) := by 
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      ring_nf
      all_goals positivity
    have h62 : (13 : ℝ ) ^ (1 / 2 : ℝ ) = Real.sqrt 13 := by 
      rw [Real.sqrt_eq_rpow]
      all_goals norm_num
    rw [h61, h62]
  have h7 : ( (9 : ℝ ) ^ ((1 : ℝ) / 4) ) ^ 2 = (3 : ℝ ) := by 
    have h71 : ( (9 : ℝ ) ^ ((1 : ℝ) / 4) ) ^ 2 = (9 ) ^ (1 / 2 : ℝ ) := by 
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      ring_nf
      all_goals positivity
    have h72 : (9 : ℝ ) ^ (1 / 2 : ℝ ) = (3 : ℝ ) := by
      rw [show (9 : ℝ ) = 3 ^ (2 : ℝ ) by norm_num]
      rw [← Real.rpow_mul]
      norm_num
      all_goals norm_num
    rw [h71, h72]
  have eq1 : ( (13 : ℝ ) ^ ((1 : ℝ) / 4 ) + (9 : ℝ ) ^ ((1 : ℝ) / 4 ) ) * ( Real.sqrt 13 + 3 ) * ( (13 : ℝ ) ^ ((1 : ℝ) / 4 ) - (9 : ℝ ) ^ ((1 : ℝ) / 4 ) ) = (4 : ℝ ) := by
    calc
      ( (13 : ℝ ) ^ ((1 : ℝ) / 4 ) + (9 : ℝ ) ^ ((1 : ℝ) / 4 ) ) * ( Real.sqrt 13 + 3 ) * ( (13 : ℝ ) ^ ((1 : ℝ) / 4 ) - (9 : ℝ ) ^ ((1 : ℝ) / 4 ) ) = ( ( (13 : ℝ ) ^ ((1 : ℝ) / 4 ) + (9 : ℝ ) ^ ((1 : ℝ) / 4 ) ) * ( (13 : ℝ ) ^ ((1 : ℝ) / 4 ) - (9 : ℝ ) ^ ((1 : ℝ) / 4 ) ) ) * ( ( Real.sqrt 13 + 3 ) ) := by ring
      _ = ( ( ( (13 : ℝ ) ^ ( (1 : ℝ ) / 4 ) ) ^ 2 - ( ( 9 : ℝ ) ^ ( (1 : ℝ ) / 4 ) ) ^ 2 ) ) * ( ( Real.sqrt 13 + 3 ) ) := by
        ring
      _ = ( ( Real.sqrt 13 ) - ( 3 : ℝ ) ) * ( ( Real.sqrt 13 + 3 ) ) := by
        have h80 : ( ( (13 : ℝ ) ^ ( (1 : ℝ ) / 4 ) ) ^ 2 ) = Real.sqrt 13 := by
          linarith [ h6 ]
        have h90 : ( ( (9 : ℝ ) ^ ( (1 : ℝ ) / 4 ) ) ^ 2 ) = (3 : ℝ ) := by
          linarith [ h7 ]
        rw [h80, h90]
        all_goals norm_num
      _ = ( ( Real.sqrt 13 ) ^ 2 - ( 3 : ℝ ) ^ 2 ) := by
        ring
      _ = ( (13 : ℝ ) - ( 9 : ℝ ) ) := by
        have h10 : Real.sqrt 13 ^ 2 = (13 : ℝ ) := Real.sq_sqrt (by norm_num)
        have h11 : (3 : ℝ ) ^ 2 = (9 : ℝ ) := by norm_num
        rw [h10, h11]
      _ = ( 4 : ℝ ) := by
        norm_num
  field_simp [h3]
  nlinarith [ Real.sqrt_pos.mpr (show (0 : ℝ) < (13 : ℝ ) by norm_num ), Real.sq_sqrt (show (0 : ℝ ) ≤ (13 : ℝ ) by norm_num ), h6, h7, Real.sqrt_nonneg 13 ]