import Mathlib

theorem algebra_2253 {x y : ℝ} (h : x ^ 2 + y ^ 2 - 4 * x - 2 * y + 5 = 0) :
    (Real.sqrt x + y) / Real.sqrt (3 * y - 2 * Real.sqrt x) = 3 + 2 * Real.sqrt 2 := by

  have h1 : (x - 2) ^ 2 + (y - 1) ^ 2 = 0 := by
    nlinarith

  have hx : x = 2 := by
    nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 1)]

  have hy : y = 1 := by
    nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 1)]

  have hx2 : Real.sqrt x = Real.sqrt 2 := by
    rw [hx]

  have h3 : 3 * y - 2 * Real.sqrt x = (Real.sqrt 2 - 1) ^ 2 := by
    rw [hy, hx2]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

  have h4 : Real.sqrt (3 * y - 2 * Real.sqrt x) = Real.sqrt 2 - 1 := by
    rw [h3]
    have h5 : 0 ≤ Real.sqrt 2 - 1 := by
      have h6 : 1 < Real.sqrt 2 := Real.lt_sqrt_of_sq_lt (by norm_num)
      linarith [Real.sqrt_nonneg 2]
    have h7 : Real.sqrt ((Real.sqrt 2 - 1) ^ 2) = Real.sqrt 2 - 1 := by
      rw [Real.sqrt_sq (by linarith [h5, Real.sqrt_nonneg 2])]
    rw [h7]

  have h8 : Real.sqrt x + y = Real.sqrt 2 + 1 := by
    rw [hx2, hy]

  have h9 : Real.sqrt 2 - 1 ≠ 0 := by
    have h10 : 1 < Real.sqrt 2 := Real.lt_sqrt_of_sq_lt (by norm_num)
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (2 : ℝ) > 0)]

  rw [h8, h4]

  field_simp [h9]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num : (2 : ℝ) ≥ 0)]