import Mathlib

theorem algebra_102609 {x : ℝ} (hx : x = √3 - √2) :
    x^7 + 3 * x^6 - 10 * x^5 - 29 * x^4 + x^3 - 2 * x^2 + x - 1 = 23 + √3 - √2 - 10 * √6 := by
  rw [hx]
  have h1 : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have h2 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h3 : (√3 : ℝ) * (√2 : ℝ) = √6 := by 
    calc
      (√3 : ℝ) * (√2 : ℝ) = √(3 * 2) := by rw [Real.sqrt_mul (by norm_num)]
      _ = √6 := by norm_num
  have h4 : (√3 - √2) ^ 2 = 5 - 2 * √6 := by 
    nlinarith [h1, h2, h3, Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sqrt_nonneg 6]
  have h5 : (√3 - √2) ^ 3 = 9 * √3 - 11 * √2 := by
    nlinarith [h1, h2, h3, Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sqrt_nonneg 6, h4]
  have h6 : (√3 - √2) ^ 4 = 49 - 20 * √6 := by
    nlinarith [h1, h2, h3, Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sqrt_nonneg 6, h5, h4]
  have h7 : (√3 - √2) ^ 5 = 89 * √3 - 109 * √2 := by 
    nlinarith [h1, h2, h3, Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sqrt_nonneg 6, h6, h5, h4]
  have h8 : (√3 - √2) ^ 6 = 485 - 198 * √6 := by 
    nlinarith [h1, h2, h3, Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sqrt_nonneg 6, h7, h5, h4]
  have h9 : (√3 - √2) ^ 7 = 881 * √3 - 1079 * √2 := by 
    nlinarith [h1, h2, h3, Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sqrt_nonneg 6, h8, h5, h4]
  nlinarith [h1, h2, h3, h4, h5, h6, h7, h8, h9, Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sqrt_nonneg 6]