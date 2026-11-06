import Mathlib

theorem algebra_322353 {x : ℝ} (hx : x = Real.sqrt (19 - 8 * Real.sqrt 3)) :
    (x ^ 4 - 6 * x ^ 3 - 2 * x ^ 2 + 18 * x + 23) / (x ^ 2 - 8 * x + 15) = 5 := by
  have h1 : x = 4 - Real.sqrt 3 := by
    rw [hx]
    have h2 : Real.sqrt (19 - 8 * Real.sqrt 3) = 4 - Real.sqrt 3 := by
      have h3 : (4 - Real.sqrt 3 : ℝ) ≥ 0 := by
        nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]
      have h4 : (4 - Real.sqrt 3 : ℝ) ^ 2 = (19 - 8 * Real.sqrt 3 : ℝ) := by
        nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      rw [← h4]
      field_simp [Real.sqrt_sq (show (0 : ℝ) ≤ 4 - Real.sqrt 3 by linarith)]
      all_goals linarith
    exact h2
  have h3 : x ^ 2 = 8 * x - 13 := by
    rw [h1]
    nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have h4 : x ^ 3 = 51 * x - 104 := by
    calc
      x ^ 3 = x * (x ^ 2) := by ring
      _ = x * (8 * x - 13) := by rw [h3]
      _ = 8 * x ^ 2 - 13 * x := by ring
      _ = 8 * (8 * x - 13) - 13 * x := by rw [h3]
      _ = 51 * x - 104 := by linarith
  have h5 : x ^ 4 = 304 * x - 663 := by
    calc
      x ^ 4 = x * (x ^ 3) := by ring
      _ = x * (51 * x - 104) := by rw [h4]
      _ = 51 * x ^ 2 - 104 * x := by ring
      _ = 51 * (8 * x - 13) - 104 * x := by rw [h3]
      _ = 304 * x - 663 := by linarith
  have h6 : x ^ 4 - 6 * x ^ 3 - 2 * x ^ 2 + 18 * x + 23 = 10 := by
    rw [h5, h4, h3]
    nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  have h7 : x ^ 2 - 8 * x + 15 = 2 := by
    have h8 : x ^ 2 - 8 * x + 13 = 0 := by linarith
    linarith
  rw [h6, h7]
  all_goals norm_num