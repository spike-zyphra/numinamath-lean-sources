import Mathlib

theorem algebra_313284 {x y : ℝ} (hx : x^2 ≥ 2008) (hy : y^2 ≥ 2008)
    (h : (x - Real.sqrt (x^2 - 2008)) * (y - Real.sqrt (y^2 - 2008)) = 2008) :
    3 * x^2 - 2 * y^2 + 3 * x - 3 * y - 2007 = 1 := by
  have h1 : x - Real.sqrt (x^2 - 2008) ≠ 0 := by
    by_contra h1
    have : (x - Real.sqrt (x^2 - 2008)) * (y - Real.sqrt (y^2 - 2008)) = 0 := by
      rw [h1]
      norm_num
    linarith
  have h2 : y - Real.sqrt (y^2 - 2008) ≠ 0 := by
    by_contra h2
    have : (x - Real.sqrt (x^2 - 2008)) * (y - Real.sqrt (y^2 - 2008)) = 0 := by
      rw [h2]
      norm_num
    linarith
  have hx0 : (x - Real.sqrt (x^2 - 2008)) * (x + Real.sqrt (x^2 - 2008)) = 2008 := by
    nlinarith [Real.sqrt_nonneg (x^2 - 2008), Real.sq_sqrt (show x^2 - 2008 ≥ 0 by linarith)]
  have hy0 : (y - Real.sqrt (y^2 - 2008)) * (y + Real.sqrt (y^2 - 2008)) = 2008 := by
    nlinarith [Real.sqrt_nonneg (y^2 - 2008), Real.sq_sqrt (show y^2 - 2008 ≥ 0 by linarith)]
  have h3 : (x + Real.sqrt (x^2 - 2008)) * (y + Real.sqrt (y^2 - 2008)) = 2008 := by
    have hx2 : (x + Real.sqrt (x^2 - 2008)) * (y + Real.sqrt (y^2 - 2008)) = 2008 ^ 2 / ((x - Real.sqrt (x^2 - 2008)) * (y - Real.sqrt (y^2 - 2008))) := by
      field_simp [h1, h2]
      <;> nlinarith [Real.sqrt_nonneg (x^2 - 2008), Real.sq_sqrt (show x^2 - 2008 ≥ 0 by linarith)]
    rw [h] at hx2
    nlinarith
  have h4 : Real.sqrt (x^2 - 2008) = 0 := by
    nlinarith [ Real.sqrt_nonneg (x^2 - 2008), Real.sqrt_nonneg (y^2 - 2008), mul_nonneg (Real.sqrt_nonneg (x^2 - 2008)) (Real.sqrt_nonneg (y^2 - 2008)), sq_nonneg (x - y), sq_nonneg (Real.sqrt (x^2 - 2008) + Real.sqrt (y^2 - 2008)), sq_nonneg (x + y), Real.sq_sqrt (show x^2 - 2008 ≥ 0 by linarith), Real.sq_sqrt (show y^2 - 2008 ≥ 0 by linarith) ]
  have h5 : x^2 = 2008 := by 
    have h5a : Real.sqrt (x^2 - 2008) = 0 := h4
    have h5b : Real.sqrt (x^2 - 2008) ^ 2 = 0 := by
      rw [h5a]
      all_goals norm_num
    have h7a : Real.sqrt (x^2 - 2008) ^ 2 = x^2 - 2008 := by 
      rw [Real.sq_sqrt]
      linarith
    nlinarith [ h5b, h7a ]
  have h7 : Real.sqrt (y^2 - 2008) = 0 := by
    nlinarith [ Real.sqrt_nonneg (x^2 - 2008), Real.sqrt_nonneg (y^2 - 2008), 
        mul_nonneg (Real.sqrt_nonneg (x^2 - 2008)) (Real.sqrt_nonneg (y^2 - 2008)), 
        sq_nonneg (x - y), sq_nonneg (Real.sqrt (x^2 - 2008) + Real.sqrt (y^2 - 2008)), sq_nonneg (x + y), h4, Real.sq_sqrt (show x^2 - 2008 ≥ 0 by linarith), Real.sq_sqrt (show y^2 - 2008 ≥ 0 by linarith) 
      ]
  have h8 : y^2 = 2008 := by 
    have h8a : Real.sqrt (y^2 - 2008) = 0 := h7
    have h8b : Real.sqrt (y^2 - 2008) ^ 2 = 0 := by 
      rw [h8a]
      all_goals norm_num
    have h8c : Real.sqrt (y^2 - 2008) ^ 2 = y^2 - 2008 := by 
      rw [Real.sq_sqrt]
      linarith
    nlinarith [ h8b, h8c ]
  nlinarith [ Real.sqrt_nonneg (x^2 - 2008), Real.sqrt_nonneg (y^2 - 2008), h4, h7, sq_nonneg (x - y), sq_nonneg (x + y), h5, h8 ]