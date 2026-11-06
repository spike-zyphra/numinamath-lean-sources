import Mathlib

open Real

theorem algebra_276300 : (2 + √3) / (√2 + √(2 + √3)) + (2 - √3) / (√2 - √(2 - √3)) = √2 := by

  have h1 : √(2 + Real.sqrt 3) = (Real.sqrt 3 + 1) / Real.sqrt 2 := by
    have h2 : ((Real.sqrt 3 + 1) / Real.sqrt 2) ^ 2 = (2 + Real.sqrt 3 : ℝ) := by 
      have h3 : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)
      have h4 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
      field_simp
      nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h10 : ((Real.sqrt 3 + 1) / Real.sqrt 2) ≥ 0 := by
      apply div_nonneg
      · -- Show that sqrt 3 + 1 ≥ 0
        nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2]
      · -- Show that sqrt 2 > 0
        positivity
    have h11 : Real.sqrt (2 + Real.sqrt 3) = (Real.sqrt 3 + 1) / Real.sqrt 2 := by
      rw [← h2]
      field_simp [Real.sqrt_nonneg (2 + Real.sqrt 3), h10]
    exact h11

  have h2 : √(2 - Real.sqrt 3) = (Real.sqrt 3 - 1) / Real.sqrt 2 := by
    have h3 : Real.sqrt (2 - Real.sqrt 3) ≥ 0 := Real.sqrt_nonneg (2 - Real.sqrt 3)
    have h4 : ((Real.sqrt 3 - 1 : ℝ) / Real.sqrt 2) ^ 2 = (2 - Real.sqrt 3 : ℝ) := by 
      have h5 : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)
      have h6 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
      field_simp
      nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h10 : (Real.sqrt 3 - 1 : ℝ) / Real.sqrt 2 ≥ 0 := by
      apply div_nonneg
      · -- Show that sqrt 3 - 1 ≥ 0
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 2]
      · -- Show that sqrt 2 > 0
        positivity
    have h11 : Real.sqrt (2 - Real.sqrt 3) = (Real.sqrt 3 - 1 : ℝ) / Real.sqrt 2 := by
      rw [← h4]
      field_simp [Real.sqrt_nonneg (2 - Real.sqrt 3), h10]
    exact h11

  rw [h1, h2]

  have h3 : Real.sqrt 2 > 0 := by
    have h4 : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)
    exact h4

  have h5 : (2 + Real.sqrt 3) / (Real.sqrt 2 + (Real.sqrt 3 + 1) / Real.sqrt 2) = (2 + Real.sqrt 3) / ( (3 + Real.sqrt 3) / Real.sqrt 2 ) := by
    have h7 : Real.sqrt 2 + (Real.sqrt 3 + 1) / Real.sqrt 2 = (3 + Real.sqrt 3) / Real.sqrt 2 := by
      field_simp
      nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    rw [h7]

  have h6 : (2 - Real.sqrt 3) / (Real.sqrt 2 - (Real.sqrt 3 - 1) / Real.sqrt 2) = (2 - Real.sqrt 3) / ( (3 - Real.sqrt 3) / Real.sqrt 2 ) := by
    have h7 : Real.sqrt 2 - (Real.sqrt 3 - 1) / Real.sqrt 2 = (3 - Real.sqrt 3) / Real.sqrt 2 := by
      field_simp
      nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    rw [h7]

  rw [h5, h6]

  have h7 : (2 + Real.sqrt 3) / ( (3 + Real.sqrt 3) / Real.sqrt 2 ) = (2 + Real.sqrt 3) / (3 + Real.sqrt 3) * Real.sqrt 2 := by
    field_simp

  have h8 : (2 - Real.sqrt 3) / ( (3 - Real.sqrt 3) / Real.sqrt 2 ) = (2 - Real.sqrt 3) / (3 - Real.sqrt 3) * Real.sqrt 2 := by
    field_simp

  rw [h7, h8]

  have h9 : (2 + Real.sqrt 3) / (3 + Real.sqrt 3) + (2 - Real.sqrt 3) / (3 - Real.sqrt 3) = 1 := by
    have h9 : (3 + Real.sqrt 3) ≠ 0 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    have h10 : (3 - Real.sqrt 3) ≠ 0 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    field_simp [h9, h10]
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]

  calc
    (2 + Real.sqrt 3) / (3 + Real.sqrt 3) * Real.sqrt 2 + (2 - Real.sqrt 3) / (3 - Real.sqrt 3) * Real.sqrt 2 
        = ( (2 + Real.sqrt 3) / (3 + Real.sqrt 3) + (2 - Real.sqrt 3) / (3 - Real.sqrt 3) ) * Real.sqrt 2 := by ring 
    _ = (1) * Real.sqrt 2 := by rw [h9]
    _ = Real.sqrt 2 := by ring