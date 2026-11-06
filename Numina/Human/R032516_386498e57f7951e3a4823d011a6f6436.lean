import Mathlib

/- Given real numbers x, y satisfy (x+√(x^2+1))(y+√(y^2+1)) ≥ 1, find the minimum value of x+y -/
theorem algebra_145460 (x y : ℝ) (h : (x + Real.sqrt (x ^ 2 + 1)) * (y + Real.sqrt (y ^ 2 + 1)) ≥ 1) :
    x + y ≥ 0 := by
  have h1 : x + Real.sqrt (x ^ 2 + 1) > 0 := by
    have h1 : Real.sqrt (x ^ 2 + 1) > |x| := by
      cases le_or_lt 0 x with
      | inl hx_nonneg =>
        rw [abs_of_nonneg hx_nonneg]
        have h3 : x ^ 2 + 1 > x ^ 2 := by linarith [sq_nonneg x]
        have h4 : Real.sqrt (x ^ 2 + 1) > Real.sqrt (x ^ 2) := Real.sqrt_lt_sqrt (by linarith [sq_nonneg x]) h3
        have h5 : Real.sqrt (x ^ 2) = x := by
          rw [Real.sqrt_sq_eq_abs]
          rw [abs_of_nonneg hx_nonneg]
        linarith [h4, h5]
      | inr hx_neg =>
        rw [abs_of_neg hx_neg]
        have h3 : x ^ 2 + 1 > x ^ 2 := by linarith [sq_nonneg x]
        have h4 : Real.sqrt (x ^ 2 + 1) > Real.sqrt (x ^ 2) := Real.sqrt_lt_sqrt (by linarith [sq_nonneg x]) h3
        have h5 : Real.sqrt (x ^ 2) = -x := by
          rw [Real.sqrt_sq_eq_abs]
          rw [abs_of_neg hx_neg]
        linarith [h4, h5]
    cases le_or_lt 0 x with
    | inl hx_nonneg =>
      have h2 : Real.sqrt (x ^ 2 + 1) > x := by
        linarith [abs_of_nonneg hx_nonneg, h1]
      nlinarith [h2]
    | inr hx_neg =>
      have h2 : Real.sqrt (x ^ 2 + 1) > -x := by
        linarith [abs_of_neg hx_neg, h1]
      nlinarith [h2]
  have h2 : y + Real.sqrt (y ^ 2 + 1) > 0 := by
    have h1 : Real.sqrt (y ^ 2 + 1) > |y| := by
      cases le_or_lt 0 y with
      | inl hy_nonneg =>
        rw [abs_of_nonneg hy_nonneg]
        have h3 : y ^ 2 + 1 > y ^ 2 := by linarith [sq_nonneg y]
        have h4 : Real.sqrt (y ^ 2 + 1) > Real.sqrt (y ^ 2) := Real.sqrt_lt_sqrt (by linarith [sq_nonneg y]) h3
        have h5 : Real.sqrt (y ^ 2) = y := by
          rw [Real.sqrt_sq_eq_abs]
          rw [abs_of_nonneg hy_nonneg]
        linarith [h4, h5]
      | inr hy_neg =>
        rw [abs_of_neg hy_neg]
        have h3 : y ^ 2 + 1 > y ^ 2 := by linarith [sq_nonneg y]
        have h4 : Real.sqrt (y ^ 2 + 1) > Real.sqrt (y ^ 2) := Real.sqrt_lt_sqrt (by linarith [sq_nonneg y]) h3
        have h5 : Real.sqrt (y ^ 2) = -y := by
          rw [Real.sqrt_sq_eq_abs]
          rw [abs_of_neg hy_neg]
        linarith [h4, h5]
    cases le_or_lt 0 y with
    | inl hy_nonneg =>
      have h2 : Real.sqrt (y ^ 2 + 1) > y := by
        linarith [abs_of_nonneg hy_nonneg, h1]
      nlinarith [h2]
    | inr hy_neg =>
      have h2 : Real.sqrt (y ^ 2 + 1) > -y := by
        linarith [abs_of_neg hy_neg, h1]
      nlinarith [h2]
  have h3 : (x + Real.sqrt (x ^ 2 + 1)) * (y + Real.sqrt (y ^ 2 + 1)) ≥ 1 := h
  nlinarith [sq_nonneg (x - y), Real.sq_sqrt (show 0 ≤ x ^ 2 + 1 by nlinarith), Real.sq_sqrt (show 0 ≤ y ^ 2 + 1 by nlinarith),
    h, h1, h2, mul_pos h1 h2]