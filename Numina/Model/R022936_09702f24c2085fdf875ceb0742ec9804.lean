import Mathlib

theorem algebra_160175 {z : ℝ} (hz : z = Real.sqrt 3 / 2) :
    (1 + z) / (1 + Real.sqrt (1 + z)) - (1 - z) / (1 - Real.sqrt (1 - z)) = Real.sqrt 3 / 3 := by
  have h1 : z = Real.sqrt 3 / 2 := hz
  have h2 : 1 + z = (2 + Real.sqrt 3) / 2 := by
    rw [h1]
    ring
  have h3 : 1 - z = (2 - Real.sqrt 3) / 2 := by
    rw [h1]
    ring
  have h4 : Real.sqrt (1 + z) = (Real.sqrt 3 + 1) / 2 := by
    rw [h2]
    have h5 : Real.sqrt ((2 + Real.sqrt 3) / 2) = (Real.sqrt 3 + 1) / 2 := by
      have h6 : ((Real.sqrt 3 + 1) / 2) ^ 2 = (2 + Real.sqrt 3) / 2 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      have h7 : (Real.sqrt 3 + 1) / 2 ≥ 0 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      rw [←h6]
      field_simp [Real.sqrt_sq (show (0 : ℝ) ≤ (Real.sqrt 3 + 1) / 2 by linarith [h7])]
    exact h5
  have h8 : Real.sqrt (1 - z) = (Real.sqrt 3 - 1) / 2 := by
    rw [h3]
    have h9 : Real.sqrt ((2 - Real.sqrt 3) / 2) = (Real.sqrt 3 - 1) / 2 := by
      have h10 : ((Real.sqrt 3 - 1) / 2) ^ 2 = (2 - Real.sqrt 3) / 2 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      have h11 : (Real.sqrt 3 - 1) / 2 ≥ 0 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      rw [←h10]
      field_simp [Real.sqrt_sq (show (0 : ℝ) ≤ (Real.sqrt 3 - 1) / 2 by linarith [h11])]
    exact h9
  have h10 : 1 + Real.sqrt (1 + z) = (3 + Real.sqrt 3) / 2 := by
    rw [h4]
    linarith
  have h11 : 1 - Real.sqrt (1 - z) = (3 - Real.sqrt 3) / 2 := by
    rw [h8]
    linarith
  rw [h10, h11, h2, h3]
  have h15 : (3 + Real.sqrt 3 : ℝ) ≠ 0 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have h16 : (3 - Real.sqrt 3 : ℝ) ≠ 0 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  field_simp [h15, h16]
  nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]