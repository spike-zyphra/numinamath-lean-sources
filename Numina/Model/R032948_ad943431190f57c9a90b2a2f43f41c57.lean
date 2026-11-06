import Mathlib

open Real

theorem algebra_196132 {x y : ℝ} (hx : x = (1 - sqrt 3) / (1 + sqrt 3)) (hy : y = (1 + sqrt 3) / (1 - sqrt 3))
    (b : ℝ) (hb : b = 2 * x ^ 2 - 3 * x * y + 2 * y ^ 2) : b = 25 := by
  have hx2 : x = -2 + Real.sqrt 3 := by
    rw [hx]
    have h1 : (1 - Real.sqrt 3 : ℝ) / (1 + Real.sqrt 3 : ℝ) = -2 + Real.sqrt 3 := by
      have h2 : (1 + Real.sqrt 3) ≠ 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      field_simp [h2]
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    exact h1
  have hy2 : y = -2 - Real.sqrt 3 := by
    rw [hy]
    have h1 : (1 + Real.sqrt 3 : ℝ) / (1 - Real.sqrt 3 : ℝ) = -2 - Real.sqrt 3 := by
      have h2 : (1 - Real.sqrt 3 : ℝ) ≠ 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      field_simp [h2]
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    exact h1
  rw [hb]
  rw [hx2, hy2]
  nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]