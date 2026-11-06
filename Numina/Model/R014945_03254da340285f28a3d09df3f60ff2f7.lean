import Mathlib

theorem inequalities_600638 (x y : ℝ) (hx : Real.sqrt 2 < x) (hy : Real.sqrt 2 < y) :
    x^4 - x^3 * y + x^2 * y^2 - x * y^3 + y^4 > x^2 + y^2 := by
  have h1 : 2 < x ^ 2 := by
    have h : Real.sqrt 2 < x := hx
    have h2 : 0 < Real.sqrt 2 := by
      positivity
    have h3 : Real.sqrt 2 ^ 2 < x ^ 2 := by
      apply pow_lt_pow_left
      all_goals nlinarith
    have h4 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    nlinarith
  have h2 : 2 < y ^ 2 := by
    have h : Real.sqrt 2 < y := hy
    have h2 : 0 < Real.sqrt 2 := by
      positivity
    have h3 : Real.sqrt 2 ^ 2 < y ^ 2 := by
      apply pow_lt_pow_left
      all_goals nlinarith
    have h4 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    nlinarith
  have h3 : 0 < x := by
    have h4 : Real.sqrt 2 > 0 := by
      positivity
    nlinarith
  have h4 : 0 < y := by
    have h5 : Real.sqrt 2 > 0 := by
      positivity
    nlinarith
  have h5 : x^4 - x^3 * y + x^2 * y^2 - x * y^3 + y^4 > x^2 + y^2 := by
    have h6 : x^2 > 2 := by nlinarith
    have h7 : y^2 > 2 := by nlinarith
    have h9 : x * y > 2 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x * y)]
    nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (x - y), sq_nonneg (x + y), 
      sq_nonneg (x * y - 2), sq_nonneg (x * y), 
      sq_nonneg (x - y), 
      sq_nonneg (x^2 + y^2 - 2), 
      mul_pos h3 h4, 
      mul_pos (show 0 < x^2 by nlinarith) (show 0 < y^2 by nlinarith), 
      sq_nonneg (x - y)
    ]
  exact h5