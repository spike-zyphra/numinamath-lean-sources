import Mathlib

theorem algebra_1060 {x y : ℝ} (h : (x + Real.sqrt (x ^ 2 + 2016)) * (y + Real.sqrt (y ^ 2 + 2016)) = 2016) :
    x + y = 0 := by
  have eq1 : (Real.sqrt (x ^ 2 + 2016)) ^ 2 = x ^ 2 + 2016 := Real.sq_sqrt (by positivity)
  have eq2 : (Real.sqrt (y ^ 2 + 2016)) ^ 2 = y ^ 2 + 2016 := Real.sq_sqrt (by positivity)
  have h_eq1 : (x + Real.sqrt (x ^ 2 + 2016)) * (Real.sqrt (x ^ 2 + 2016) - x) = 2016 := by
    nlinarith [sq_nonneg (Real.sqrt (x ^ 2 + 2016) - x), Real.sqrt_nonneg (x ^ 2 + 2016)]
  have h_eq2 : (y + Real.sqrt (y ^ 2 + 2016)) * (Real.sqrt (y ^ 2 + 2016) - y) = 2016 := by
    nlinarith [sq_nonneg (Real.sqrt (y ^ 2 + 2016) - y), Real.sqrt_nonneg (y ^ 2 + 2016)]
  have hne1 : x + Real.sqrt (x ^ 2 + 2016) ≠ 0 := by
    by_contra hne
    have : (x + Real.sqrt (x ^ 2 + 2016)) * (Real.sqrt (x ^ 2 + 2016) - x) = 0 := by
      rw [hne]
      norm_num
    linarith [h_eq1, this]
  have hne4 : y + Real.sqrt (y ^ 2 + 2016) ≠ 0 := by
    by_contra hne
    have : (y + Real.sqrt (y ^ 2 + 2016)) * (Real.sqrt (y ^ 2 + 2016) - y) = 0 := by
      rw [hne]
      norm_num
    linarith [h_eq2, this]
  -- Now by manipulation we can solving.
  have h3 : y + Real.sqrt (y ^ 2 + 2016) = Real.sqrt (x ^ 2 + 2016) - x := by
    apply (mul_left_inj' hne1).mp
    linarith 
  have h_eq3 : (y + Real.sqrt (y ^ 2 + 2016)) ^ 2 = (Real.sqrt (x ^ 2 + 2016) - x) ^ 2 := by 
    rw [h3]
  -- Now by expanding and equating to reach goal
  nlinarith [sq_nonneg (Real.sqrt (x ^ 2 + 2016) - Real.sqrt (y ^ 2 + 2016)), sq_nonneg (x + y), 
      Real.sqrt_nonneg (x ^ 2 + 2016), Real.sqrt_nonneg (y ^ 2 + 2016), 
      mul_nonneg (Real.sqrt_nonneg (x ^ 2 + 2016)) (Real.sqrt_nonneg (y ^ 2 + 2016)), 
      h_eq3, mul_nonneg (Real.sqrt_nonneg (x ^ 2 + 2016)) (Real.sqrt_nonneg (y ^ 2 + 2016))]