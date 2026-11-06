import Mathlib

theorem algebra_196624 {x : ℝ} (hx : x = Real.sqrt (7 - 4 * Real.sqrt 3)) :
    (x^2 - 4 * x + 5) / (x^2 - 4 * x + 3) = 2 := by

  have h1 : Real.sqrt (7 - 4 * Real.sqrt 3) = 2 - Real.sqrt 3 := by
    have h2 : (2 - Real.sqrt 3 : ℝ) ^ 2 = 7 - 4 * Real.sqrt 3 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    have h3 : (2 - Real.sqrt 3 : ℝ) ≥ 0 := by
      have h4 : Real.sqrt 3 ≤ 2 := by
        have h5 : Real.sqrt 3 ≤ Real.sqrt (4 : ℝ) := Real.sqrt_le_sqrt (by norm_num)
        have h6 : Real.sqrt (4 : ℝ) = 2 := Real.sqrt_eq_cases.mpr (by norm_num)
        linarith
      linarith [Real.sqrt_nonneg 3]
    rw [← h2]
    field_simp [Real.sqrt_sq h3]
  rw [hx, h1]
  have h2 : ( (2 - Real.sqrt 3) ^ 2 - 4 * (2 - Real.sqrt 3) + 5 ) = 4 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]
  have h3 : ( (2 - Real.sqrt 3) ^ 2 - 4 * (2 - Real.sqrt 3) + 3 ) = 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]
  rw [h2, h3]
  all_goals norm_num