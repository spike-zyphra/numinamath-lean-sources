import Mathlib

theorem algebra_303780 (x : ℝ) (hx : x = Real.sqrt (19 - 8 * Real.sqrt 3)) :
    ((x^4 - 6 * x^3 - 2 * x^2 + 18 * x + 23) / (x^3 - 7 * x^2 + 5 * x + 15)) = 5 := by
  have h1 : x = 4 - Real.sqrt 3 := by
    rw [hx]
    have h2 : Real.sqrt (19 - 8 * Real.sqrt 3) = 4 - Real.sqrt 3 := by
      have h3 : (4 - Real.sqrt 3) ^ 2 = 19 - 8 * Real.sqrt 3 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
      have h4 : 0 ≤ (4 - Real.sqrt 3 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3]
      rw [← h3]
      field_simp [Real.sqrt_sq, h4]
    exact h2
  rw [h1]
  have h2 : (4 - Real.sqrt 3 : ℝ) ^ 2 = 8 * (4 - Real.sqrt 3) - 13 := by
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
  have h3 : (4 - Real.sqrt 3 : ℝ) ^ 3 = 51 * (4 - Real.sqrt 3) - 104 := by
    calc
      (4 - Real.sqrt 3 : ℝ) ^ 3 = (4 - Real.sqrt 3) * ((4 - Real.sqrt 3) ^ 2) := by ring
      _ = (4 - Real.sqrt 3) * (8 * (4 - Real.sqrt 3) - 13) := by rw [h2]
      _ = 51 * (4 - Real.sqrt 3) - 104 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
  have h4 : (4 - Real.sqrt 3 : ℝ) ^ 4 = 304 * (4 - Real.sqrt 3) - 663 := by
    calc
      (4 - Real.sqrt 3 : ℝ) ^ 4 = (4 - Real.sqrt 3) * ((4 - Real.sqrt 3 : ℝ) ^ 3) := by ring
      _ = (4 - Real.sqrt 3) * (51 * (4 - Real.sqrt 3) - 104) := by rw [h3]
      _ = 304 * (4 - Real.sqrt 3) - 663 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
  have h5 : (4 - Real.sqrt 3 : ℝ) ^ 4 - 6 * (4 - Real.sqrt 3 : ℝ) ^ 3 - 2 * (4 - Real.sqrt 3 : ℝ) ^ 2 + 18 * (4 - Real.sqrt 3 : ℝ) + 23 = 10 := by
    rw [h4, h3, h2]
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
  have h6 : (4 - Real.sqrt 3 : ℝ) ^ 3 - 7 * (4 - Real.sqrt 3 : ℝ) ^ 2 + 5 * (4 - Real.sqrt 3 : ℝ) + 15 = 2 := by
    rw [h3, h2]
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
  rw [h5, h6]
  all_goals norm_num