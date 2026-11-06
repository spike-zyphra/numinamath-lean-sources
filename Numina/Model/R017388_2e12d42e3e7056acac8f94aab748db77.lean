import Mathlib

theorem algebra_313298 {x : ℝ} (hx : x = Real.sqrt 3 - 2) :
    ((-x^2 - 2 * x) / (x^2 - 1)) / ((1 / (abs x + 1)) + (1 / (abs x - 1))) =
    Real.sqrt 3 / 2 := by

  have h1 : x < 0 := by
    rw [hx]
    have h2 : Real.sqrt 3 < 2 := by
      nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    nlinarith

  have h2 : abs x = (2 - Real.sqrt 3 : ℝ) := by
    rw [abs_of_neg h1]
    linarith [hx]

  have h3 : x ^ 2 = (7 - 4 * Real.sqrt 3 : ℝ) := by
    rw [hx]
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]

  have h4 : -x^2 - 2 * x = (-3 + 2 * Real.sqrt 3 : ℝ) := by
    rw [h3]
    rw [hx]
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]

  have h5 : x^2 - 1 = (6 - 4 * Real.sqrt 3 : ℝ) := by
    rw [h3]
    nlinarith

  have h6 : (-x^2 - 2 * x) / (x^2 - 1) = (-1 / 2 : ℝ) := by
    rw [h4, h5]
    have h7 : (6 - 4 * Real.sqrt 3 : ℝ) ≠ 0 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (3 : ℝ) > (0 : ℝ) by norm_num)]
    field_simp [h7]
    <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]

  have h7 : abs x + 1 = (3 - Real.sqrt 3 : ℝ) := by
    rw [h2]
    nlinarith

  have h8 : abs x - 1 = (1 - Real.sqrt 3 : ℝ) := by
    rw [h2]
    nlinarith

  have h9 : (1 / (abs x + 1)) + (1 / (abs x - 1)) = (-Real.sqrt 3 / 3 : ℝ) := by
    rw [h7, h8]
    have h10 : (3 - Real.sqrt 3 : ℝ) ≠ 0 := by
      nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    have h11 : (1 - Real.sqrt 3 : ℝ) ≠ 0 := by
      nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    field_simp [h10, h11, show Real.sqrt 3 ≠ 0 by positivity]
    <;> nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]

  rw [h6, h9]

  have h10 : Real.sqrt 3 > 0 := Real.sqrt_pos.mpr (by norm_num)
  field_simp [show Real.sqrt 3 ≠ 0 by positivity]
  <;> nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]