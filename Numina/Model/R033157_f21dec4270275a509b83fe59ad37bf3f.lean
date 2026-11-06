import Mathlib

theorem algebra_233833 : ((6 + 4 * √2) / (√2 + √(6 + 4 * √2)) +
    (6 - 4 * √2) / (√2 - √(6 - 4 * √2))) ^ 2 = 8 := by

  have h1 : √(6 + 4 * √2) = √2 + 2 := by
    have h2 : (√2 + 2) ^ 2 = 6 + 4 * √2 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    have h3 : √(6 + 4 * √2) = √((√2 + 2) ^ 2) := by
      rw [h2]
    have h4 : √((√2 + 2) ^ 2) = √2 + 2 := by
      rw [Real.sqrt_sq (show 0 ≤ √2 + 2 by
        have h5 : √2 ≥ 0 := Real.sqrt_nonneg 2
        linarith
      )]
    rw [h3, h4]

  have h2 : √(6 - 4 * √2) = 2 - √2 := by
    have h3 : (2 - √2) ^ 2 = 6 - 4 * √2 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    have h4 : √(6 - 4 * √2) = √((2 - √2) ^ 2) := by
      rw [h3]
    have h5 : √((2 - √2) ^ 2) = (2 - √2 : ℝ) := by
      rw [Real.sqrt_sq (show 0 ≤ (2 - √2 : ℝ) by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), Real.sqrt_nonneg 2]
      )]
    rw [h4, h5]

  rw [h1, h2]

  have h3 : ((6 + 4 * √2) / (√2 + (√2 + 2)) + (6 - 4 * √2) / (√2 - (2 - √2))) = 2 * √2 := by
    field_simp [(show √2 + (√2 + 2) ≠ 0 by positivity), (show √2 - (2 - √2) ≠ 0 by nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ))])]
    <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ)), sq_nonneg (√2 - 2), sq_nonneg (√2 + 2)]

  rw [h3]

  have h4 : (2 * √2) ^ 2 = 8 := by
    calc
      (2 * √2) ^ 2 = 4 * (√2 ^ 2) := by ring
      _ = 4 * 2 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
      _ = 8 := by norm_num
  rw [h4]