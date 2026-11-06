import Mathlib


/-- What is the value of a for which 1/log_2 a+1/log_3 a+1/log_4 a=1?
    (A) 9(B) 12(C) 18(D) 24(E) 36 -/
theorem algebra_96491 {a : ℝ} (ha : 0 < a) (ha' : a ≠ 1) :
    1 / Real.logb 2 a + 1 / Real.logb 3 a + 1 / Real.logb 4 a = 1 ↔ a = 24 := by
  -- We use the base change formula to show that log_a b = log_b b/log_b a = 1/log_b a.
  -- Thus our equation becomes log_a 2 + log_a 3 + log_a 24 = 1
  rw[one_div, one_div, one_div, Real.inv_logb, Real.inv_logb, Real.inv_logb,
  -- which becomes log_a (2 * 3 * 4) = 1
     ← Real.logb_mul, ← Real.logb_mul]
  -- which becomes after combining: log_a 24 = 1.
  -- Hence a = 24.
  rw[Real.logb_eq_iff_rpow_eq]
  · norm_num
  · assumption
  · assumption
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num