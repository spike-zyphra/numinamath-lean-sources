import Mathlib

theorem algebra_597771 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x^2 + y^2 / 2 = 1) :
    x * Real.sqrt (1 + y^2) ≤ 3 * Real.sqrt 2 / 4 := by

  have h1 : 0 ≤ 1 + y^2 := by
    nlinarith [show 0 ≤ y from hy]

  have h2 : Real.sqrt (1 + y^2) ≥ 0 := Real.sqrt_nonneg (1 + y^2)

  have h3 : x * Real.sqrt (1 + y^2) ≥ 0 := by
    apply mul_nonneg
    exact hx
    exact h2

  have h4 : (x * Real.sqrt (1 + y^2)) ^ 2 ≤ (9 / 8 : ℝ) := by
    have h5 : (x * Real.sqrt (1 + y^2)) ^ 2 = x ^ 2 * (1 + y ^ 2) := by
      calc
        (x * Real.sqrt (1 + y^2)) ^ 2 = x^2 * (Real.sqrt (1 + y^2) ^ 2) := by ring
        _ = x^2 * (1 + y^2) := by rw [Real.sq_sqrt (by nlinarith)]
    nlinarith [sq_nonneg (x^2 - 3 / 4), sq_nonneg (y ^ 2 - 1 / 2), sq_nonneg (4 * x ^ 2 - 3), sq_nonneg (y ^ 2 - 1), 
          h, h1, Real.sqrt_nonneg (1 + y^2), mul_nonneg (Real.sqrt_nonneg (1 + y^2)) (Real.sqrt_nonneg (1 + y^2))]

  have h5 : 0 ≤ (9 / 8 : ℝ) := by nlinarith

  have h7 : x * Real.sqrt (1 + y^2) ≤ Real.sqrt (9 / 8 : ℝ) := by
    apply Real.le_sqrt_of_sq_le 
    linarith [h4]

  have h8 : Real.sqrt (9 / 8 : ℝ) = 3 * Real.sqrt 2 / 4 := by
    have h11 : Real.sqrt (9 / 8 : ℝ) = Real.sqrt 9 / Real.sqrt 8 := by
      rw [← Real.sqrt_div (by norm_num)]
    have h12 : Real.sqrt (9 : ℝ) = 3 := by 
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h13 : Real.sqrt (8 : ℝ) = 2 * Real.sqrt 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    rw [h11, h12, h13]
    field_simp
    <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]

  nlinarith [Real.sqrt_nonneg (9 / 8), h7, h8]