import Mathlib

theorem algebra_248975 (x y : ℝ) (hx : 1 - x ≥ 0) (hy : 2 - y ≥ 0)
    (h : Real.sqrt (1 - x) + Real.sqrt (2 - y) = Real.sqrt (3 * x + 2 * y - 7)) :
    x = 1 ∧ y = 2 := by
  have h1 : (Real.sqrt (1 - x) + Real.sqrt (2 - y)) ^ 2 = (Real.sqrt (3 * x + 2 * y - 7)) ^ 2 := by
    rw [h]

  have h2 : (Real.sqrt (1 - x) + Real.sqrt (2 - y)) ^ 2 = (Real.sqrt (1 - x)) ^ 2 + (Real.sqrt (2 - y)) ^ 2 + 2 * (Real.sqrt (1 - x) * Real.sqrt (2 - y)) := by
    ring

  have h3 : (Real.sqrt (3 * x + 2 * y - 7)) ^ 2 = 3 * x + 2 * y - 7 := by
    have h4 : 3 * x + 2 * y - 7 ≥ 0 := by
      by_contra h4
      push_neg at h4
      have h5 : Real.sqrt (3 * x + 2 * y - 7) = 0 := by
        rw [Real.sqrt_eq_zero'.mpr]
        linarith
      rw [h5] at h
      have h6 : Real.sqrt (1 - x) = 0 := by
        nlinarith [Real.sqrt_nonneg (1 - x), Real.sqrt_nonneg (2 - y), h]
      have h7 : Real.sqrt (2 - y) = 0 := by
        nlinarith [Real.sqrt_nonneg (1 - x), Real.sqrt_nonneg (2 - y), h, h6]
      have hx1 : x = 1 := by
        have h8 : Real.sqrt (1 - x) = 0 := h6
        rw [Real.sqrt_eq_zero (by linarith)] at h8
        linarith
      have hy1 : y = 2 := by
        have h9 : Real.sqrt (2 - y) = 0 := h7
        rw [Real.sqrt_eq_zero (by linarith)] at h9
        linarith
      nlinarith
    rw [Real.sq_sqrt]
    linarith

  rw [h2] at h1
  rw [h3] at h1

  have h4' : (Real.sqrt (1 - x)) ^ 2 = 1 - x := by 
    rw [Real.sq_sqrt] 
    linarith

  have h5' : (Real.sqrt (2 - y)) ^ 2 = 2 - y := by 
    rw [Real.sq_sqrt] 
    linarith

  have h6 : Real.sqrt (1 - x) * Real.sqrt (2 - y) = Real.sqrt ((1 - x) * (2 - y)) := by 
    rw [← Real.sqrt_mul (by linarith)]

  have h5 : 10 - 4 * x - 3 * y + 2 * Real.sqrt ((1 - x) * (2 - y)) = 0 := by 
    nlinarith [h1, h4', h5', h6]

  have h6' : Real.sqrt ((1 - x) * (2 - y)) = 2 * x + 3 / 2 * y - 5 := by 
    linarith

  have h7 : 2 * x + 3 / 2 * y - 5 ≥ 0 := by 
    have h8 : Real.sqrt ((1 - x) * (2 - y)) ≥ 0 := Real.sqrt_nonneg ((1 - x) * (2 - y))
    linarith [h6', h8]

  have h8 : Real.sqrt ((1 - x) * (2 - y)) ^ 2 = (2 * x + 3 / 2 * y - 5) ^ 2 := by 
    rw [h6']
  
  have h9 : Real.sqrt ((1 - x) * (2 - y)) ^ 2 = (1 - x) * (2 - y) := by 
    apply Real.sq_sqrt
    nlinarith

  have h10 : (x - 1) ^ 2 + (y - 2) ^ 2 = 0 := by 
    nlinarith

  have hx2 : (x - 1) ^ 2 = 0 := by 
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 2), h10]

  have hy2 : (y - 2) ^ 2 = 0 := by 
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 2), h10]

  have hx3 : x - 1 = 0 := by 
    apply pow_eq_zero 
    exact hx2

  have hy3 : y - 2 = 0 := by 
    apply pow_eq_zero 
    exact hy2

  have hx4 : x = 1 := by linarith 
  have hy4 : y = 2 := by linarith 
  constructor 
  · exact hx4 
  · exact hy4