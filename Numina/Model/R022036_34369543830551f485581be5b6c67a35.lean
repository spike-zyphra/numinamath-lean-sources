import Mathlib

theorem algebra_310645 {x : ℝ} (hx : x = Real.sqrt (19 - 8 * Real.sqrt 3)) :
    ((x ^ 4 - 6 * x ^ 3 - 2 * x ^ 2 + 18 * x + 23) / (x ^ 2 - 8 * x + 15)) = 5 := by
  have h1 : x = 4 - Real.sqrt 3 := by
    rw [hx]
    have h2 : Real.sqrt (19 - 8 * Real.sqrt 3) = 4 - Real.sqrt 3 := by
      have h3 : (4 - Real.sqrt 3 : ℝ) ^ 2 = 19 - 8 * Real.sqrt 3 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (0 : ℝ) < (3 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ))]
      have h4 : 0 ≤ (4 - Real.sqrt 3 : ℝ) := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (0 : ℝ) < (3 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ))]
      rw [←h3]
      field_simp [Real.sqrt_sq]
      all_goals nlinarith [Real.sqrt_nonneg 3]
    linarith
  have h3 : x ^ 2 - 8 * x + 15 = 2 := by
    rw [h1]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (0 : ℝ) < (3 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ))]
  have h4 : x ^ 4 - 6 * x ^ 3 - 2 * x ^ 2 + 18 * x + 23 = 10 := by
    rw [h1]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (0 : ℝ) < (3 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ))]
  have h5 : (x ^ 4 - 6 * x ^ 3 - 2 * x ^ 2 + 18 * x + 23) / (x ^ 2 - 8 * x + 15) = 5 := by
    rw [h4, h3]
    all_goals norm_num
  exact h5