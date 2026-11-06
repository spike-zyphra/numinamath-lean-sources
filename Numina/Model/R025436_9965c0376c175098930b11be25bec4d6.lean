import Mathlib

theorem algebra_322479 {a : ℝ} (ha : a = (-Real.sqrt 6 + Real.sqrt (6 - 4 * Real.sqrt 2)) / 2) :
    a^3 + Real.sqrt 6 * a^2 + Real.sqrt 2 * a + Real.sqrt 6 = Real.sqrt 6 := by
  have h1 : Real.sqrt (6 - 4 * Real.sqrt 2) = 2 - Real.sqrt 2 := by
    have h2 : (2 - Real.sqrt 2 : ℝ) ^ 2 = 6 - 4 * Real.sqrt 2 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h3 : (2 - Real.sqrt 2 : ℝ) ≥ 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    rw [←h2]
    field_simp [Real.sqrt_sq, h3]
  have ha2 : a = (2 - Real.sqrt 6 - Real.sqrt 2) / 2 := by
    rw [ha, h1]
    ring_nf
  rw [ha2]
  nlinarith [sq_nonneg ((2 - Real.sqrt 6 - Real.sqrt 2) / 2 + (Real.sqrt 6 + Real.sqrt 2) / 2 - 1),
            Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num),
            Real.sqrt_pos.mpr (show (0 : ℝ) < 6 by norm_num),
            Real.sqrt_nonneg 2, Real.sqrt_nonneg 6, Real.sqrt_nonneg (6 - 4 * Real.sqrt 2),
            Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num),
            Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num),
            Real.sq_sqrt (show (0 : ℝ) ≤ (6 - 4 * Real.sqrt 2 : ℝ) by
              nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
            )
           ]