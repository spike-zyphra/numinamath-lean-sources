import Mathlib

theorem algebra_10297 : (Real.sqrt 2 / Real.sqrt 5) * (Real.sqrt 3 / Real.sqrt 6) * (Real.sqrt 4 / Real.sqrt 7) = 2 * Real.sqrt 35 / 35 := by
  have h1 : Real.sqrt 2 / Real.sqrt 5 = Real.sqrt (2 / 5) := by
    field_simp [Real.sqrt_div]
  have h2 : Real.sqrt 3 / Real.sqrt 6 = Real.sqrt (3 / 6) := by
    field_simp [Real.sqrt_div]
  have h3 : Real.sqrt 4 / Real.sqrt 7 = Real.sqrt (4 / 7) := by
    field_simp [Real.sqrt_div]
  rw [h1, h2, h3]
  have h4 : Real.sqrt (2 / 5 : ℝ) * Real.sqrt (3 / 6 : ℝ) * Real.sqrt (4 / 7 : ℝ) = Real.sqrt ((2 / 5 : ℝ) * (3 / 6 : ℝ) * (4 / 7 : ℝ)) := by
    rw [← Real.sqrt_mul (by norm_num)]
    rw [← Real.sqrt_mul (by norm_num)]
    all_goals norm_num
  rw [h4]
  have h5 : (2 / 5 : ℝ) * (3 / 6 : ℝ) * (4 / 7 : ℝ) = (4 / 35 : ℝ) := by norm_num
  rw [h5]
  have h6 : Real.sqrt (4 / 35 : ℝ) = (2 * Real.sqrt 35 / 35 : ℝ) := by
    have h9a : Real.sqrt (4 / 35 : ℝ) ≥ 0 := Real.sqrt_nonneg (4 / 35)
    have h10a : (2 * Real.sqrt 35 / 35 : ℝ) ≥ 0 := by
      have h17a : Real.sqrt 35 ≥ 0 := Real.sqrt_nonneg 35
      nlinarith [show Real.sqrt 35 > 0 by positivity]
    have h11a : Real.sqrt (4 / 35 : ℝ) ^ 2 = (4 / 35 : ℝ) := by
      rw [Real.sq_sqrt]
      all_goals norm_num
    have h12a : (2 * Real.sqrt 35 / 35 : ℝ) ^ 2 = (4 / 35 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 35, Real.sq_sqrt (show (0 : ℝ) ≤ 35 by norm_num)]
    have h13a : Real.sqrt (4 / 35 : ℝ) ^ 2 = (2 * Real.sqrt 35 / 35 : ℝ) ^ 2 := by
      rw [h11a, h12a]
    have h14a : Real.sqrt (4 / 35 : ℝ) = (2 * Real.sqrt 35 / 35 : ℝ) := by
      nlinarith [show Real.sqrt (4 / 35 : ℝ) ≥ 0 by apply Real.sqrt_nonneg, show (2 * Real.sqrt 35 / 35 : ℝ) ≥ 0 by positivity]
    exact h14a
  exact h6