import Mathlib

theorem algebra_2812 {x y : ℝ}
    (hx : x = (Real.sqrt 3 + Real.sqrt 2) / (Real.sqrt 3 - Real.sqrt 2))
    (hy : y = (Real.sqrt 3 - Real.sqrt 2) / (Real.sqrt 3 + Real.sqrt 2)) :
    x / y + y / x = 98 := by
  have h1 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h3 : Real.sqrt 3 - Real.sqrt 2 ≠ 0 := by
    have h4 : Real.sqrt 3 > Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  have h4 : Real.sqrt 3 + Real.sqrt 2 ≠ 0 := by
    have h5 : Real.sqrt 3 > 0 := Real.sqrt_pos.mpr (by norm_num)
    have h6 : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num)
    linarith [h5, h6]
  have h5 : x = (Real.sqrt 3 + Real.sqrt 2) / (Real.sqrt 3 - Real.sqrt 2) := by exact hx
  have h6 : y = (Real.sqrt 3 - Real.sqrt 2) / (Real.sqrt 3 + Real.sqrt 2) := by exact hy
  have h7 : x + y = 10 := by
    rw [h5, h6]
    have h8 : (Real.sqrt 3 - Real.sqrt 2) * (Real.sqrt 3 + Real.sqrt 2) = 1 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), mul_pos h1 h2]
    field_simp [(show Real.sqrt 3 - Real.sqrt 2 ≠ 0 by exact h3), (show Real.sqrt 3 + Real.sqrt 2 ≠ 0 by exact h4), h8]
    nlinarith [sq_nonneg (Real.sqrt 3), sq_nonneg (Real.sqrt 2), Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (Real.sqrt 3 - Real.sqrt 2), sq_nonneg (Real.sqrt 3 + Real.sqrt 2)]
  have h8 : x * y = 1 := by 
    rw [h5, h6]
    have h9 : (Real.sqrt 3 - Real.sqrt 2) * (Real.sqrt 3 + Real.sqrt 2) = 1 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), mul_pos h1 h2]
    field_simp [(show Real.sqrt 3 - Real.sqrt 2 ≠ 0 by exact h3), (show Real.sqrt 3 + Real.sqrt 2 ≠ 0 by exact h4), h9]
  have h9 : x / y + y / x = x^2 + y ^ 2 := by
    have h10 : x * y = 1 := h8
    have hxne : x ≠ 0 := by
      by_contra h
      rw [h] at h8
      nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, mul_pos h1 h2]
    have hyne : y ≠ 0 := by 
      by_contra h
      rw [h] at h8
      nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, mul_pos h1 h2]
    have eq1 : x / y + y / x = (x^2 + y^2) / (x * y) := by
      field_simp [hxne, hyne]
      <;> nlinarith
    have eq2 : (x^2 + y^2) / (x * y) = x^2 + y ^ 2 := by
      rw [show x * y = (1 : ℝ) by linarith]
      field_simp
    rw [eq1, eq2]
  have h10 : x^2 + y^2 = 98 := by 
    have h11 : x + y = 10 := h7
    have h12 : x * y = 1 := h8
    calc 
      x^2 + y^2 = (x + y) ^ 2 - 2 * (x * y) := by nlinarith
      _ = (10) ^ 2 - 2 * (1) := by rw [h11, h12]
      _ = 98 := by norm_num
  rw [h9]
  linarith [h10]