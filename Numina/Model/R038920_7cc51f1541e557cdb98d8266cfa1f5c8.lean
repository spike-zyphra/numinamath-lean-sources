import Mathlib

theorem algebra_299132 : (2 + Real.sqrt 5) ^ ((1 : ℝ) / 3) / (1 + Real.sqrt 5) = 1 / 2 := by

  have h1 : 0 < (1 + Real.sqrt 5) := by
    have h2 : 0 < (Real.sqrt 5) := Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num)
    linarith
  have h2 : (2 + Real.sqrt 5) = ((1 + Real.sqrt 5) / 2) ^ 3 := by
    ring_nf
    have h51 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have h52 : Real.sqrt 5 ^ 3 = Real.sqrt 5 * 5 := by
      calc
        Real.sqrt 5 ^ 3 = Real.sqrt 5 * (Real.sqrt 5 ^ 2) := by ring
        _ = Real.sqrt 5 * 5 := by rw [h51]
    nlinarith [h51, h52, Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num)]
  have h3 : (2 + Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3) = (1 + Real.sqrt 5) / 2 := by
    have h4 : (2 + Real.sqrt 5 : ℝ) = ((1 + Real.sqrt 5) / 2) ^ 3 := h2
    have h6 : ((2 + Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3)) = ((( (1 + Real.sqrt 5 ) / 2 ) ^ 3 ) ^ ((1 : ℝ) / 3) ) := by rw [h4]
    rw [h6]
    have h7 : ((( (1 + Real.sqrt 5 ) / 2 ) ^ 3 ) ^ ((1 : ℝ) / 3) ) = ( (1 + Real.sqrt 5 ) / 2 ) := by
      have h8 : ( ( (1 + Real.sqrt 5 ) / 2 ) ^ 3 ) ≥ 0 := by positivity
      have h9 : ( ( ( (1 + Real.sqrt 5 ) / 2 ) ^ 3 ) ^ ( (1 : ℝ ) / 3 ) ) = ( (1 + Real.sqrt 5 ) / 2 ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals nlinarith [Real.sqrt_nonneg (5 : ℝ)]
      linarith
    exact h7
  rw [h3]
  have h5 : (1 + Real.sqrt 5) > 0 := by
    have h51 : Real.sqrt 5 > 0 := by positivity
    linarith
  field_simp [h5]
  <;> nlinarith [Real.sqrt_nonneg (5 : ℝ)]