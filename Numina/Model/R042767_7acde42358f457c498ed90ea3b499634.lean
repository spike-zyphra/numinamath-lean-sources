import Mathlib

theorem algebra_7364 {x : ℝ} (hx : x = (Real.sqrt 5 + 1) / (Real.sqrt 5 - 1)) :
    ⌊x⌋^2 + (x - ⌊x⌋)^2 + (1 / 2) * ⌊x⌋ * (x - ⌊x⌋) = 5 := by

  have h1 : x = (3 + Real.sqrt 5) / 2 := by
    rw [hx]
    have h2 : Real.sqrt 5 - 1 ≠ 0 := by
      nlinarith [Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num : (5 : ℝ) ≥ 0)]
    field_simp [(show Real.sqrt 5 - 1 ≠ 0 by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num : (5 : ℝ) ≥ 0)]
    )]
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num : (5 : ℝ) ≥ 0), sq_nonneg (Real.sqrt 5 - 2)]

  have h4 : ⌊(3 + Real.sqrt 5) / 2⌋ = 2 := by
    have h6 : 2 < (3 + Real.sqrt 5) / 2 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num : (0 : ℝ) ≤ (5 : ℝ)), sq_nonneg (Real.sqrt 5 - 2)]
    have h7 : (3 + Real.sqrt 5) / 2 < 3 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num : (0 : ℝ) ≤ (5 : ℝ)), sq_nonneg (Real.sqrt 5 - 2)]
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> nlinarith

  rw [h1]
  rw [h4]
  nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num : (0 : ℝ) ≤ (5 : ℝ))]