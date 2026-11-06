import Mathlib

theorem algebra_251126 {x y : ℝ} (h : (x + Real.sqrt (x ^ 2 + 1)) * (y + Real.sqrt (y ^ 2 + 1)) = 1) : x + y = 0 := by
  have eq6 : (x + Real.sqrt (x ^ 2 + 1)) * (y + Real.sqrt (y ^ 2 + 1)) = 1 := h
  -- note that for any real number t, we have: 
  -- (t + sqrt(t^2 + 1))(sqrt(t^2 + 1) - t) = (sqrt(t^2 + 1)^2) - t^2 = (t^2 + 1) - t^2 = 1
  have eq8 : (x + Real.sqrt (x ^ 2 + 1)) * (Real.sqrt (x ^ 2 + 1) - x) = 1 := by
    nlinarith [Real.sqrt_nonneg (x ^ 2 + 1), Real.sqrt_nonneg (y ^ 2 + 1), Real.sq_sqrt (show 0 ≤ x ^ 2 + 1 by positivity), Real.sq_sqrt (show 0 ≤ y ^ 2 + 1 by positivity), sq_nonneg (Real.sqrt (x ^ 2 + 1) ^ 2 - x ^ 2), sq_nonneg (x + y)]
  -- so we can derive $y + \sqrt(y^2 + 1) = \sqrt(x^2 + 1) - x$.
  -- because of eq6 and eq8, so we have $(x + \sqrt(x^2 + 1))(y + \sqrt(y^2 + 1)) = (x + \sqrt(x^2 + 1))*(\sqrt(x^2 + 1) - x) = 1$.
  have eq10 : y + Real.sqrt (y ^ 2 + 1) = Real.sqrt (x ^ 2 + 1) - x := by
    have h11 : (x + Real.sqrt (x ^ 2 + 1)) * (y + Real.sqrt (y ^ 2 + 1)) = 1 := by nlinarith
    have h10 : (x + Real.sqrt (x ^ 2 + 1)) * (Real.sqrt (x ^ 2 + 1) - x) = 1 := by nlinarith
    have h22 : (x + Real.sqrt (x ^ 2 + 1)) * (y + Real.sqrt (y ^ 2 + 1)) = (x + Real.sqrt (x ^ 2 + 1)) * (Real.sqrt (x ^ 2 + 1) - x) := by nlinarith
    have h33 : (x + Real.sqrt (x ^ 2 + 1)) ≠ 0 := by
      by_contra h111
      have : (x + Real.sqrt (x ^ 2 + 1)) * (y + Real.sqrt (y ^ 2 + 1)) = 0 := by
        rw [h111]
        norm_num
      nlinarith
    have h44 : y + Real.sqrt (y ^ 2 + 1) = Real.sqrt (x ^ 2 + 1) - x := by
      apply (mul_left_inj' h33).mp
      linarith
    linarith
  -- rearrange to get $x + y + \sqrt(y^2 + 1) = \sqrt(x^2 + 1)$.
  have eq12 : x + y + Real.sqrt (y ^ 2 + 1) = Real.sqrt (x ^ 2 + 1) := by
    nlinarith [Real.sqrt_nonneg (x ^ 2 + 1), Real.sqrt_nonneg (y ^ 2 + 1)]
  -- now we square both side.
  -- left side squared: (x + y + \sqrt(y^2 + 1))^2 = (x + y)^2 + 2(x + y)\sqrt(y^2 + 1) + (y^2 + 1).
  -- right side squared: (x^2 + 1)
  have eq14 : (x + y + Real.sqrt (y ^ 2 + 1))^2 = (Real.sqrt (x ^ 2 + 1))^2 := by
    rw [eq12]
  have eq16 : (x + y + Real.sqrt (y ^ 2 + 1))^2 = (x + y)^2 + 2 * (x + y) * Real.sqrt (y ^ 2 + 1) + (Real.sqrt (y ^ 2 + 1) ) ^2 := by
    ring
  rw [eq16] at eq14
  have h7 : Real.sqrt (y ^ 2 + 1) ^ 2 = y ^ 2 + 1 := Real.sq_sqrt (show 0 ≤ y ^ 2 + 1 by positivity)
  have h8 : Real.sqrt (x ^ 2 + 1) ^ 2 = x ^ 2 + 1 := Real.sq_sqrt (show 0 ≤ x ^ 2 + 1 by positivity)
  nlinarith [Real.sqrt_nonneg (x ^ 2 + 1), Real.sqrt_nonneg (y ^ 2 + 1), sq_nonneg (x + y), sq_nonneg (x - (-y)), Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 + 1 by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ y ^ 2 + 1 by positivity)]