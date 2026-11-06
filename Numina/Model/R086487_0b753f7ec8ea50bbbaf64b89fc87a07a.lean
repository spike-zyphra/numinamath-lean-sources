import Mathlib

theorem algebra_242667 : (1 : ℝ) / 2016 < (1 / Real.sqrt 2016) ∧
    (1 / Real.sqrt 2016) < 1 ∧ 1 < Real.sqrt 2016 ∧ Real.sqrt 2016 < 2016 := by
  have h1 : 0 < (2016 : ℝ) := by norm_num
  have h2 : 0 < Real.sqrt 2016 := Real.sqrt_pos.mpr (show (2016 : ℝ) > 0 by norm_num)

  have h3 : Real.sqrt 2016 < (2016 : ℝ) := by
    have h4 : Real.sqrt 2016 ^ 2 = (2016 : ℝ) := Real.sq_sqrt (by norm_num)
    have h5 : 0 < Real.sqrt 2016 := Real.sqrt_pos.mpr (show (2016 : ℝ) > 0 by norm_num)
    nlinarith [Real.sqrt_nonneg 2016, sq_pos_of_pos h5, h4, Real.sqrt_nonneg 2016]

  have h6 : (1 : ℝ) < Real.sqrt 2016 := by
    have h7 : Real.sqrt 2016 ^ 2 = (2016 : ℝ) := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 2016, sq_pos_of_pos (show (0 : ℝ) < Real.sqrt 2016 by positivity), h7]

  have h8 : (1 : ℝ) / 2016 < (1 / Real.sqrt 2016) := by
    have h9 : 0 < Real.sqrt 2016 := Real.sqrt_pos.mpr (show (2016 : ℝ) > 0 by norm_num)
    have h10 : 0 < (2016 : ℝ) := by norm_num
    apply (div_lt_div_iff (by positivity) (by positivity)).mpr
    nlinarith [Real.sqrt_pos.mpr (show (2016 : ℝ) > 0 by norm_num), h3]

  have h9 : (1 / Real.sqrt 2016) < 1 := by
    have h10 : Real.sqrt 2016 > 1 := h6
    have h5 : 0 < Real.sqrt 2016 := Real.sqrt_pos.mpr (show (2016 : ℝ) > 0 by norm_num)
    apply (div_lt_iff (by positivity)).mpr
    nlinarith [Real.sqrt_pos.mpr (show (2016 : ℝ) > 0 by norm_num)]

  have h12 : 1 < Real.sqrt 2016 := h6

  have h4 : Real.sqrt 2016 < (2016 : ℝ) := h3

  constructor
  · -- Show that (1 : ℝ) / 2016 < (1 / Real.sqrt 2016)
    exact h8
  constructor
  · -- Show that (1 / Real.sqrt 2016) < 1
    exact h9
  constructor
  · -- Show that 1 < Real.sqrt 2016
    exact h6
  · -- Show that Real.sqrt 2016 < 2016
    exact h3