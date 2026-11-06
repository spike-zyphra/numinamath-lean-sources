import Mathlib

theorem algebra_288143 {x : ℝ}
    (hx : x = (2009 ^ ((1 : ℝ) / 3) - 1 / 2009 ^ ((1 : ℝ) / 3)) / 2) :
    (x + Real.sqrt (1 + x ^ 2)) ^ 3 = 2009 := by

  have h1 : x = (( (2009 : ℝ) ^ ((1 : ℝ) / 3) - 1 / (2009 : ℝ) ^ ((1 : ℝ) / 3) ) ) / 2 := by
    simpa using hx

  have h3_eq : 1 + x ^ 2 = (( (2009 : ℝ) ^ ((1 : ℝ) / 3) + 1 / (2009 : ℝ) ^ ((1 : ℝ) / 3) ) ) ^ 2 / 4 := by
    rw [h1]
    have h4 : ( ( (2009 : ℝ) ^ ((1 : ℝ) / 3) - 1 / (2009 : ℝ) ^ ((1 : ℝ) / 3) ) ) ^ 2 = ( ( (2009 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 2 - 2 + ( 1 / (2009 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 2 ) := by 
      field_simp
      <;> nlinarith 
    have h4' : ( ( (2009 : ℝ) ^ ((1 : ℝ) / 3) + 1 / (2009 : ℝ) ^ ((1 : ℝ) / 3) ) ) ^ 2 = ( ( (2009 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 2 + 2 + ( 1 / (2009 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 2 ) := by 
      field_simp
      <;> nlinarith 
    nlinarith [ h4, h4', sq_nonneg ( ( (2009 : ℝ) ^ ((1 : ℝ) / 3) ) - 1 ), sq_nonneg ( ( (2009 : ℝ) ^ ((1 : ℝ) / 3) ) + 1 ), Real.rpow_nonneg (show 0 ≤ (2009 : ℝ) by norm_num) (1 / 3) ]

  have h4 : Real.sqrt (1 + x ^ 2) = ( ( (2009 : ℝ) ^ ((1 : ℝ) / 3) + 1 / (2009 : ℝ) ^ ((1 : ℝ) / 3) ) ) / 2 := by 
    have h7 : Real.sqrt (1 + x ^ 2) = Real.sqrt ( (( (2009 : ℝ) ^ ((1 : ℝ) / 3) + 1 / (2009 : ℝ) ^ ((1 : ℝ) / 3) ) ) ^ 2 / 4 ) := by 
      rw [h3_eq]
    rw [h7]
    have h8 : ( ( (2009 : ℝ) ^ ((1 : ℝ) / 3) + 1 / (2009 : ℝ) ^ ((1 : ℝ) / 3) ) ) ≥ 0 := by 
      have h9 : ( (2009 : ℝ) ^ ((1 : ℝ) / 3) ) > 0 := by positivity
      have h10 : (1 / (2009 : ℝ) ^ ((1 : ℝ) / 3) ) > 0 := by positivity
      linarith
    have h9 : Real.sqrt ( (( (2009 : ℝ) ^ ((1 : ℝ) / 3) + 1 / (2009 : ℝ) ^ ((1 : ℝ) / 3) ) ) ^ 2 / 4 ) = ( ( (2009 : ℝ) ^ ((1 : ℝ) / 3) + 1 / (2009 : ℝ) ^ ((1 : ℝ) / 3) ) ) / 2 := by 
      have h10 : Real.sqrt ( (( (2009 : ℝ) ^ ((1 : ℝ) / 3) + 1 / (2009 : ℝ) ^ ((1 : ℝ) / 3) ) ) ^ 2 / 4 ) = Real.sqrt ( (( (2009 : ℝ) ^ ((1 : ℝ) / 3) + 1 / (2009 : ℝ) ^ ((1 : ℝ) / 3) ) ) ^ 2 ) / Real.sqrt ( (4 : ℝ) ) := by 
        field_simp [Real.sqrt_div]
        all_goals linarith
      have h11 : Real.sqrt ( (( (2009 : ℝ) ^ ((1 : ℝ) / 3) + 1 / (2009 : ℝ) ^ ((1 : ℝ) / 3) ) ) ^ 2 ) = ( (2009 : ℝ) ^ ((1 : ℝ) / 3) + 1 / (2009 : ℝ) ^ ((1 : ℝ) / 3) ) := by 
        rw [Real.sqrt_sq (show ( (2009 : ℝ) ^ ((1 : ℝ) / 3) + 1 / (2009 : ℝ) ^ ((1 : ℝ) / 3) ) ≥ 0 by linarith [h8] ) ]
      have h12 : Real.sqrt ( (4 : ℝ) ) = 2 := by 
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
      rw [h11, h12] at h10 
      linarith 
    linarith

  have h5 : x + Real.sqrt (1 + x ^ 2) = ( (2009 : ℝ) ^ ((1 : ℝ) / 3) ) := by
    rw [h4] 
    rw [h1]
    field_simp
    <;> ring

  rw [h5]
  have h6 : (( (2009 : ℝ) ^ ((1 : ℝ) / 3) ) ) ^ 3 = (2009 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num 
    all_goals norm_num

  exact h6