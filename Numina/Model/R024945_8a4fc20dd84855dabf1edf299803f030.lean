import Mathlib

theorem algebra_187722 (x : ℝ) (hx : x = (9 + 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3) + (9 - 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3)) :
    x = 3 := by
  have h1 : x = (9 + 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3) + (9 - 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3) := by 
    exact hx
  have h2 : x^3 = 18 + 3 * x := by
    rw [h1]
    have h3 : ((9 + 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3) + (9 - 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 =
        ((9 + 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 + ((9 - 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 + 3 * ((9 + 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3) * ((9 - 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3)) ) * ((9 + 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3) + (9 - 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3)) := by
      ring
    rw [h3] 
    have h4 : ((9 + 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (9 + 4 * Real.sqrt 5 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals nlinarith [Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num : (5 : ℝ) ≥ 0)]
    have h5 : ((9 - 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (9 - 4 * Real.sqrt 5 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals nlinarith [Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num : (5 : ℝ) ≥ 0)]
    have h6 : ((9 + 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3)) * ((9 - 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3)) = 1 := by
      have h7 : ((9 + 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3)) * ((9 - 4 * Real.sqrt 5 : ℝ) ^ ((1 : ℝ) / 3)) = ((9 + 4 * Real.sqrt 5 : ℝ) * (9 - 4 * Real.sqrt 5 : ℝ)) ^ ((1 : ℝ) / 3) := by
        rw [← Real.mul_rpow]
        all_goals nlinarith [Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num) ]
      rw [h7]
      have h8 : (9 + 4 * Real.sqrt 5 : ℝ) * (9 - 4 * Real.sqrt 5 : ℝ) = 1 := by
        nlinarith [Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num), Real.sq_sqrt (show (5: ℝ) ≥ 0 by norm_num)]
      rw [h8]
      norm_num
    rw [h4, h5, h6]
    all_goals nlinarith
  have h3 : x^3 - 3 * x - 18 = 0 := by
    linarith [h2]
  have h4 : (x - 3) * (x^2 + 3 * x + 6) = 0 := by
    nlinarith [h3]
  cases' (mul_eq_zero.mp h4) with h5 h6
  · -- Case where x - 3 = 0, so x = 3
    linarith 
  · -- Case where x^2 + 3 x + 6 = 0, which has no real solution
    have h7 : (x^2 + 3 * x + 6 : ℝ) = 0 := by
      linarith [h6]
    have h8 : (x^2 + 3 * x + 6 : ℝ) > 0 := by
      nlinarith [sq_nonneg (x + 3 / 2)]
    nlinarith