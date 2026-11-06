import Mathlib

theorem algebra_97166 {x : ℝ} (hx : x^2 - 1 ≥ 0) (h : x + Real.sqrt (x^2 - 1) + 1 / (x - Real.sqrt (x^2 - 1)) = 20) :
    x^2 + Real.sqrt (x^4 - 1) + 1 / (x^2 + Real.sqrt (x^4 - 1)) = 51.005 := by

  have h1 : x - Real.sqrt (x ^ 2 - 1) ≠ 0 := by
    by_contra h1
    have h2 : x = Real.sqrt (x ^ 2 - 1) := by linarith [h1]
    have h3 : Real.sqrt (x ^ 2 - 1) ≥ 0 := by positivity
    have h4 : Real.sqrt (x ^ 2 - 1) ^ 2 = x ^ 2 - 1 := by
      rw [Real.sq_sqrt]
      linarith
    have h5 : x ^ 2 = x ^ 2 - 1 := by
      have h6 : Real.sqrt (x ^ 2 - 1) = x := by linarith [h2]
      rw [h6] at h4
      nlinarith [h4]
    nlinarith

  have h1' : 1 / (x - Real.sqrt (x ^ 2 - 1)) = x + Real.sqrt (x ^ 2 - 1) := by
    have h8 : x - Real.sqrt (x ^ 2 - 1) ≠ 0 := h1
    field_simp [h8]
    nlinarith [Real.sqrt_nonneg (x ^ 2 - 1), Real.sq_sqrt (show x ^ 2 - 1 ≥ 0 by linarith [hx]), sq_nonneg (x ^ 2 - 1)]
  
  have h2 : x + Real.sqrt (x ^ 2 - 1) = 10 := by 
    rw [h1'] at h
    linarith

  have h3 : Real.sqrt (x ^ 2 - 1) = 10 - x := by
    nlinarith [Real.sqrt_nonneg (x ^ 2 - 1)]

  have h4 : x = 101 / 20 := by
    have h5 : Real.sqrt (x ^ 2 - 1) ^ 2 = (10 - x) ^ 2 := by 
      rw [h3]
    have h6 : Real.sqrt (x ^ 2 - 1) ^ 2 = x ^ 2 - 1 := by
      rw [Real.sq_sqrt]
      linarith
    rw [h6] at h5
    nlinarith

  have h7 : x ^ 2 + Real.sqrt (x ^ 4 - 1) + 1 / (x ^ 2 + Real.sqrt (x ^ 4 - 1)) = 2 * x ^ 2 := by
    have h8 : x ^ 2 + Real.sqrt (x ^ 4 - 1) ≠ 0 := by
      have h9 : x ^ 2 > 0 := by
        nlinarith [show x = 101 / 20 from h4]
      have h10 : Real.sqrt (x ^ 4 - 1) ≥ 0 := by positivity
      nlinarith
    have h12 : 1 / (x ^ 2 + Real.sqrt (x ^ 4 - 1)) = x ^ 2 - Real.sqrt (x ^ 4 - 1) := by
      have h16 : x ^ 2 + Real.sqrt (x ^ 4 - 1) ≠ 0 := h8
      field_simp [h16]
      nlinarith [Real.sqrt_nonneg (x ^ 4 - 1), Real.sq_sqrt (show x ^ 4 - 1 ≥ 0 by
        nlinarith [sq_nonneg (x ^ 2 - 1), h4]
      ), sq_nonneg (x ^ 2 ^ 2 - 1)]
    rw [h12]
    nlinarith [Real.sqrt_nonneg (x ^ 4 - 1), Real.sq_sqrt (show x ^ 4 - 1 ≥ 0 by
      nlinarith [sq_nonneg (x ^ 2 - 1), h4]
    )]

  rw [h7]
  rw [h4]
  norm_num