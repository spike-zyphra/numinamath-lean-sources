import Mathlib

theorem algebra_165711 {x : ℝ} (hx : x = (2 + Real.sqrt 3) ^ ((1 : ℝ) / 5) + (2 - Real.sqrt 3) ^ ((1 : ℝ) / 5)) :
    x^5 - 5 * x^3 + 5 * x - 4 = 0 := by
  have h1 : x = (2 + Real.sqrt 3) ^ ((1 : ℝ) / 5) + (2 - Real.sqrt 3) ^ ((1 : ℝ) / 5) := hx
  have h2 : ((2 + Real.sqrt 3) ^ ((1 : ℝ) / 5) ) ^ 5 = 2 + Real.sqrt 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals
      positivity

  have h3 : ((2 - Real.sqrt 3) ^ ((1 : ℝ) / 5) ) ^ 5 = 2 - Real.sqrt 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals
      have h4 : (2 - Real.sqrt 3 : ℝ) > 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      positivity

  have h5 : ((2 + Real.sqrt 3) ^ ((1 : ℝ) / 5) ) * ((2 - Real.sqrt 3) ^ ((1 : ℝ) / 5) ) = 1 := by
    have h6 : ((2 + Real.sqrt 3) ^ ((1 : ℝ) / 5) ) * ((2 - Real.sqrt 3) ^ ((1 : ℝ) / 5) ) =
        ((2 + Real.sqrt 3) * (2 - Real.sqrt 3)) ^ ((1 : ℝ) / 5) := by
      rw [← Real.mul_rpow]
      all_goals
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    rw [h6]
    have h7 : (2 + Real.sqrt 3 : ℝ) * (2 - Real.sqrt 3) = 1 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    rw [h7]
    norm_num

  have h8 : ((2 + Real.sqrt 3) ^ ((1 : ℝ) / 5) ) ^ 3 + ((2 - Real.sqrt 3) ^ ((1 : ℝ) / 5) ) ^ 3 = x^3 - 3 * x := by
    have h5' : ((2 + Real.sqrt 3) ^ ((1 : ℝ) / 5) ) * ((2 - Real.sqrt 3) ^ ((1 : ℝ) / 5) ) = 1 := h5
    have h7 : ((2 + Real.sqrt 3) ^ ((1 : ℝ) / 5) ) ^ 3 + ((2 - Real.sqrt 3) ^ ((1 : ℝ) / 5) ) ^ 3 = 
      ((2 + Real.sqrt 3) ^ ((1 : ℝ) / 5) + (2 - Real.sqrt 3) ^ ((1 : ℝ) / 5) ) ^ 3 - 3 * ((2 + Real.sqrt 3) ^ ((1 : ℝ) / 5) * ((2 - Real.sqrt 3) ^ ((1 : ℝ) / 5) ) ) * ((2 + Real.sqrt 3) ^ ((1 : ℝ) / 5) + (2 - Real.sqrt 3) ^ ((1 : ℝ) / 5) ) := by 
        ring
    rw [h7, h5', h1]
    <;> linarith

  have h9 : x^5 = 4 + 5 * (( (2 + Real.sqrt 3) ^ ((1 : ℝ) / 5) ) ^ 3 + ( (2 - Real.sqrt 3) ^ ((1 : ℝ) / 5) ) ^ 3 ) + 10 * x := by 
    calc
      x^5 = (( (2 + Real.sqrt 3) ^ ((1 : ℝ) / 5) ) + ( (2 - Real.sqrt 3) ^ ((1 : ℝ) / 5) ) ) ^ 5 := by 
        rw [h1]
      _ = (( (2 + Real.sqrt 3) ^ ((1 : ℝ) / 5) ) ^ 5 + ( (2 - Real.sqrt 3) ^ ((1 : ℝ) / 5) ) ^ 5 ) + 5 * (( (2 + Real.sqrt 3) ^ ((1 : ℝ) / 5) ) * ( (2 - Real.sqrt 3) ^ ((1 : ℝ) / 5) ) ) * (( (2 + Real.sqrt 3) ^ ((1 : ℝ) / 5) ) ^ 3 + ( (2 - Real.sqrt 3) ^ ((1 : ℝ) / 5) ) ^ 3 ) + 10 * (( (2 + Real.sqrt 3) ^ ((1 : ℝ) / 5) ) * ( (2 - Real.sqrt 3) ^ ((1 : ℝ) / 5) ) ) ^ 2 * (( (2 + Real.sqrt 3) ^ ((1 : ℝ) / 5) ) + ( (2 - Real.sqrt 3) ^ ((1 : ℝ) / 5) ) ) := by 
        ring
      _ = (2 + Real.sqrt 3 + (2 - Real.sqrt 3)) + 5 * (( (2 + Real.sqrt 3) ^ ((1 : ℝ) / 5) ) * ( (2 - Real.sqrt 3) ^ ((1 : ℝ) / 5) ) ) * (( (2 + Real.sqrt 3) ^ ((1 : ℝ) / 5) ) ^ 3 + ( (2 - Real.sqrt 3) ^ ((1 : ℝ) / 5) ) ^ 3 ) + 10 * (( (2 + Real.sqrt 3) ^ ((1 : ℝ) / 5) ) * ( (2 - Real.sqrt 3) ^ ((1 : ℝ) / 5) ) ) ^ 2 * x := by 
        rw [h2, h3, h1]
      _ = 4 + 5 * (( (2 + Real.sqrt 3) ^ ((1 : ℝ) / 5) ) * ( (2 - Real.sqrt 3) ^ ((1 : ℝ) / 5) ) ) * (( (2 + Real.sqrt 3) ^ ((1 : ℝ) / 5) ) ^ 3 + ( (2 - Real.sqrt 3) ^ ((1 : ℝ) / 5) ) ^ 3 ) + 10 * (( (2 + Real.sqrt 3) ^ ((1 : ℝ) / 5) ) * ( (2 - Real.sqrt 3) ^ ((1 : ℝ) / 5) ) ) ^ 2 * x := by 
        ring_nf
      _ = 4 + 5 * (1) * (( (2 + Real.sqrt 3) ^ ((1 : ℝ) / 5) ) ^ 3 + ( (2 - Real.sqrt 3) ^ ((1 : ℝ) / 5) ) ^ 3 ) + 10 * (1) ^ 2 * x := by
        rw [h5]
      _ = 4 + 5 * (( (2 + Real.sqrt 3) ^ ((1 : ℝ) / 5) ) ^ 3 + ( (2 - Real.sqrt 3) ^ ((1 : ℝ) / 5) ) ^ 3 ) + 10 * x := by 
        ring

  rw [h9, h8]
  <;> nlinarith [sq_nonneg (x^2 - 1), sq_nonneg (x - 1), sq_nonneg (( (2 + Real.sqrt 3) ^ ((1 : ℝ) / 5) ) - ( (2 - Real.sqrt 3) ^ ((1 : ℝ) / 5) ) ), sq_nonneg (x^2 - 2), sq_nonneg (x + 1), sq_nonneg (x - 2) ]