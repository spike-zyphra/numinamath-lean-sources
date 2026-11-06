import Mathlib

theorem algebra_15326 {x y : ℝ} (h1 : y = (x + 1)^2) (h2 : x + 4 = (y - 3)^2)
    (r : ℝ) (hr : r > 0) (h : ∀ x y, (x + 1)^2 = y ∧ x + 4 = (y - 3)^2 →
    (x - (-1))^2 + (y - 3)^2 = r^2) :
    r^2 = 13 / 2 := by

  have h3 := h 0 1 (by
    constructor
    · norm_num
    · norm_num
  )
  have eq1 : (0 - (-1) : ℝ) ^ 2 + (1 - 3 : ℝ) ^ 2 = r ^ 2 := by
    simpa using h3
  have eq2 : r^2 = 5 := by
    nlinarith

  have h5 := h ((-1 + Real.sqrt 13) / 2) ((7 + Real.sqrt 13) / 2) (by
    constructor
    · nlinarith [Real.sqrt_pos.mpr (show (13 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
    · nlinarith [Real.sqrt_pos.mpr (show (13 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
  )
  have eq5 : ((-1 + Real.sqrt 13) / 2 - (-1) : ℝ) ^ 2 + ((7 + Real.sqrt 13) / 2 - 3 : ℝ) ^ 2 = r ^ 2 := by
    simpa using h5

  have eq6 : r ^ 2 = 7 + Real.sqrt 13 := by
    nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]

  nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (13 : ℝ) by norm_num)]