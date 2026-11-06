import Mathlib

theorem algebra_285437 : √(21 + 12 * √3) - √(21 - 12 * √3) = 6 := by
  have h1 : √(21 + 12 * √3) = 2 * √3 + 3 := by
    have h2 : (2 * √3 + 3) ^ 2 = 21 + 12 * √3 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    have h3 : 0 ≤ (2 * √3 + 3 : ℝ) := by
      nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    have h4 : √(21 + 12 * √3) = 2 * √3 + 3 := by
      have h5 : √((2 * √3 + 3) ^ 2) = 2 * √3 + 3 := by 
        rw [Real.sqrt_sq (show (0 : ℝ) ≤ 2 * √3 + 3 by linarith)]
      have h6 : (21 + 12 * √3) = (2 * √3 + 3) ^ 2 := by linarith [h2]
      rw [h6] at *
      linarith [h5]
    exact h4
  have h5 : √(21 - 12 * √3) = 2 * √3 - 3 := by
    have h6 : (2 * √3 - 3) ^ 2 = 21 - 12 * √3 := by 
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    have h7 : 0 ≤ (2 * √3 - 3 : ℝ) := by
      have h8 : Real.sqrt 3 ≥ Real.sqrt (9 / 4 : ℝ) := by
        apply Real.sqrt_le_sqrt
        norm_num
      have h9 : Real.sqrt (9 / 4 : ℝ) = 3 / 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h10 : Real.sqrt 3 ≥ 3 / 2 := by
        linarith [h8, h9]
      nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    have h11 : √(21 - 12 * √3) = 2 * √3 - 3 := by 
      have h12 : √((2 * √3 - 3) ^ 2) = 2 * √3 - 3 := by 
        rw [Real.sqrt_sq (show (0 : ℝ) ≤ 2 * √3 - 3 by linarith)]
      have h13 : (21 - 12 * √3) = (2 * √3 - 3) ^ 2 := by linarith [h6]
      rw [h13]
      linarith [h12]
    exact h11
  rw [h1, h5]
  ring