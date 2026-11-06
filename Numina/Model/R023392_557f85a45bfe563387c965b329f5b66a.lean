import Mathlib

theorem algebra_313633 {x y : ℝ} (h : (x + √(x^2 + 1)) * (y + √(y^2 + 1)) = 1) : x + y = 0 := by 
  have h1 : x + √(x^2 + 1) ≠ 0 := by
    by_contra h1
    have h_eq : (x + √(x^2 + 1)) * (y + √(y^2 + 1)) = 0 := by
      rw [h1]
      norm_num
    linarith
  have h2 : y + √(y^2 + 1) ≠ 0 := by
    by_contra h2
    have h_eq : (x + √(x^2 + 1)) * (y + √(y^2 + 1)) = 0 := by
      rw [h2]
      norm_num
    linarith
  have h3 : x + √(x^2 + 1) > 0 := by
    have h4 : √(x^2 + 1) > -x := by
      by_cases h5 : -x < 0
      · nlinarith [Real.sqrt_nonneg (x^2 + 1), Real.sq_sqrt (show x^2 + 1 ≥ 0 by nlinarith), sq_nonneg (x + √(x^2 + 1)), sq_nonneg (x - √(x^2 + 1))]
      by_cases h6 : -x > 0
      · nlinarith [Real.sqrt_nonneg (x^2 + 1), Real.sq_sqrt (show x^2 + 1 ≥ 0 by nlinarith), sq_nonneg (x + √(x^2 + 1)), sq_nonneg (x - √(x^2 + 1))]
      · -- -x = 0
        have : x = 0 := by linarith
        rw [this]
        norm_num [Real.sqrt_nonneg, Real.sq_sqrt]
    nlinarith
  have h4 : y + √(y^2 + 1) > 0 := by
    have h5 : √(y^2 + 1) > -y := by
      by_cases h6 : -y < 0
      · nlinarith [Real.sqrt_nonneg (y^2 + 1), Real.sq_sqrt (show y^2 + 1 ≥ 0 by nlinarith), sq_nonneg (y + √(y^2 + 1)), sq_nonneg (y - √(y^2 + 1))]
      by_cases h7 : -y > 0
      · nlinarith [Real.sqrt_nonneg (y^2 + 1), Real.sq_sqrt (show y^2 + 1 ≥ 0 by nlinarith), sq_nonneg (y + √(y^2 + 1)), sq_nonneg (y - √(y^2 + 1))]
      · -- -y = 0
        have : y = 0 := by linarith
        rw [this]
        norm_num [Real.sqrt_nonneg, Real.sq_sqrt]
    nlinarith
  have h7 : x + y = 0 := by
    nlinarith [Real.sqrt_nonneg (x^2 + 1), Real.sqrt_nonneg (y^2 + 1), 
              mul_nonneg (Real.sqrt_nonneg (x^2 + 1)) (Real.sqrt_nonneg (y^2 + 1)), 
              sq_nonneg (x - y), sq_nonneg (x + y), 
              sq_nonneg ((x + √(x^2 + 1)) - (y + √(y^2 + 1))), 
              Real.sq_sqrt (show x^2 + 1 ≥ 0 by nlinarith), 
              Real.sq_sqrt (show y^2 + 1 ≥ 0 by nlinarith)]
  linarith