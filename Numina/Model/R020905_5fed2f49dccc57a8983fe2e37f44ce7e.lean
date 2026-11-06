import Mathlib

theorem algebra_3948 {x : ℝ}
  (hx : x  = (Real.sqrt 2020 - 1 / Real.sqrt 2020) / 2) :
    x + Real.sqrt (x ^ 2 + 1) = Real.sqrt 2020 := by

  have h1 : x ^ 2 + 1 = (Real.sqrt 2020 + 1 / Real.sqrt 2020) ^ 2 / 4 := by
    rw [hx]
    field_simp [Real.sqrt_pos.mpr (show 0 < 2020 by norm_num)]
    <;> nlinarith [Real.sqrt_nonneg 2020, Real.sq_sqrt (show 0 ≤ (2020 : ℝ) by norm_num)]

  have h2 : Real.sqrt (x ^ 2 + 1) = (Real.sqrt 2020 + 1 / Real.sqrt 2020) / 2 := by
    rw [h1]
    rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [Real.sqrt_nonneg 2020, Real.sqrt_nonneg (x ^ 2 + 1), Real.sq_sqrt (show 0 ≤ (2020 : ℝ) by norm_num), Real.sqrt_pos.mpr (show 0 < (2020 : ℝ) by norm_num)]

  rw [h2]
  rw [hx]
  field_simp [Real.sqrt_pos.mpr (show 0 < 2020 by norm_num)]
  <;> nlinarith [Real.sqrt_nonneg 2020, Real.sqrt_pos.mpr (show 0 < (2020 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2020 : ℝ) by norm_num)]