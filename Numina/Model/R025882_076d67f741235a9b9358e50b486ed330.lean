import Mathlib

open Real

theorem algebra_189207 (x y k : ℝ) (hx : 0 < x) (hy : 0 < y) (hk : 0 < k)
    (h : 3 = k^2 * (x^2 / y^2 + y^2 / x^2) + k * (x / y + y / x)) :
    k ≤ (-1 + sqrt 7) / 2 := by

  have h1 : 0 < x * y := by
    nlinarith
  
  have h2 : x^2 / y^2 + y^2 / x^2 ≥ 2 := by
    have h3 : x^2 / y^2 + y^2 / x^2 - 2 ≥ 0 := by
      have h4 : x^2 / y^2 + y^2 / x^2 - 2 = (x^2 - y^2) ^ 2 / (x^2 * y^2) := by
        field_simp
        ring
      rw [h4]
      have h5 : (x^2 - y^2) ^ 2 ≥ 0 := by
        apply sq_nonneg
      have h6 : x^2 * y^2 > 0 := by
        positivity
      apply div_nonneg
      linarith
      positivity
    linarith
  
  have h3 : x / y + y / x ≥ 2 := by 
    have h4 : x / y + y / x - 2 ≥ 0 := by 
      have h5 : x / y + y / x - 2 = (x - y) ^ 2 / (x * y) := by 
        field_simp
        ring 
      rw [h5]
      have h6 : (x - y) ^ 2 ≥ 0 := by
        apply sq_nonneg 
      have h7 : x * y > 0 := by
        positivity 
      apply div_nonneg 
      linarith 
      positivity 
    linarith

  have h4 : k^2 * (x^2 / y^2 + y^2 / x^2) + k * (x / y + y / x) = 3 := by 
    linarith [h]

  have h5 : k^2 * (x^2 / y^2 + y^2 / x^2) + k * (x / y + y / x) ≥ 2 * k^2 + 2 * k := by 
    have h6 : k^2 * (x^2 / y^2 + y^2 / x^2) ≥ k^2 * 2 := by 
      have h7 : x^2 / y^2 + y^2 / x^2 ≥ 2 := h2 
      have hk2 : k^2 > 0 := by 
        nlinarith 
      nlinarith 
    have h8 : k * (x / y + y / x) ≥ k * 2 := by 
      have h9 : x / y + y / x ≥ 2 := h3 
      have hk2 : k > 0 := hk 
      nlinarith 
    nlinarith [h6, h8]

  have h6 : 2 * k^2 + 2 * k - 3 ≤ 0 := by 
    nlinarith [h4, h5]

  have h8 : k ≤ (-1 + Real.sqrt 7) / 2 := by 
    nlinarith [h6, Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), sq_nonneg (k - (-1 + Real.sqrt 7) / 2), Real.sqrt_pos.mpr (show (0: ℝ) < 7 by norm_num)]

  exact h8