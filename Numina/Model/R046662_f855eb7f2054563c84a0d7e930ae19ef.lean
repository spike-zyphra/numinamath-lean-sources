import Mathlib

open Real

theorem algebra_118097 {a b : ℝ}
    (ha : a = (sqrt 5 + sqrt 3)^2)
    (hb : b = (sqrt 5 - sqrt 3)^(-2 : ℤ)) :
    (a + b) / (a - b) = 5 / 3 := by

  have ha2 : a = 8 + 2 * Real.sqrt 15 := by
    rw [ha]
    have h1 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have h2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have h3 : Real.sqrt 5 * Real.sqrt 3 = Real.sqrt 15 := by
      have h4 : Real.sqrt 15 = Real.sqrt (5 * 3) := by
        norm_num
      rw [h4]
      field_simp [Real.sqrt_mul]
    nlinarith [sq_nonneg (Real.sqrt 5 - Real.sqrt 3), Real.sqrt_nonneg 5, Real.sqrt_nonneg 3, h3]

  have hb2 : b = (4 + Real.sqrt 15) / 2 := by
    rw [hb]
    have h1 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have h2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have h3 : Real.sqrt 5 * Real.sqrt 3 = Real.sqrt 15 := by
      have h4 : Real.sqrt 15 = Real.sqrt (5 * 3) := by
        norm_num
      rw [h4]
      field_simp [Real.sqrt_mul]
    have h4 : (sqrt 5 - sqrt 3 : ℝ) ≠ 0 := by
      nlinarith [Real.sqrt_pos.mpr (show 5 > 0 by norm_num : (5 : ℝ) > 0), Real.sqrt_pos.mpr (show 3 > 0 by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num : (5 : ℝ) ≥ 0), Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num : (3 : ℝ) ≥ 0)]
    have h5 : (sqrt 5 - sqrt 3 : ℝ) ^ 2 = 8 - 2 * Real.sqrt 15 := by
      nlinarith [h1, h2, h3, Real.sqrt_nonneg 15, Real.sq_sqrt (show (15 : ℝ) ≥ 0 by norm_num : (15 : ℝ) ≥ 0)]
    simp [zpow_neg, zpow_ofNat, h5]
    field_simp [(show 8 - 2 * Real.sqrt 15 ≠ 0 by
      nlinarith [Real.sqrt_pos.mpr (show (15 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (15 : ℝ) ≥ 0 by norm_num)]
    )]
    <;> nlinarith [Real.sqrt_pos.mpr (show (15 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (15 : ℝ) ≥ 0 by norm_num)]

  have h6 : a - b > 0 := by
    rw [ha2, hb2]
    nlinarith [Real.sqrt_pos.mpr (show (15 : ℝ) > 0 by norm_num), Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (15 : ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num)]

  have h7 : a + b = (5 / 2) * (4 + Real.sqrt 15) := by
    rw [ha2, hb2]
    nlinarith [Real.sqrt_nonneg 15, Real.sq_sqrt (show (15 : ℝ) ≥ 0 by norm_num : (15 : ℝ) ≥ 0)]

  have h8 : a - b = (3 / 2) * (4 + Real.sqrt 15) := by
    rw [ha2, hb2]
    nlinarith [Real.sqrt_nonneg 15, Real.sq_sqrt (show (15 : ℝ) ≥ 0 by norm_num : (15 : ℝ) ≥ 0)]

  have h9 : (a + b) / (a - b) = 5 / 3 := by
    rw [h7, h8]
    have h10 : 4 + Real.sqrt 15 > 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (15 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (15 : ℝ) ≥ 0 by norm_num)]
    have h11 : (4 + Real.sqrt 15) ≠ 0 := by linarith
    field_simp [h11]
    <;> nlinarith [Real.sqrt_pos.mpr (show (15 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (15 : ℝ) ≥ 0 by norm_num)]

  exact h9