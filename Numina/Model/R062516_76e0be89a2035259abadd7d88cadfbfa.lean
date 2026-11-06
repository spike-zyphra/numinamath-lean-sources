import Mathlib

theorem algebra_143152 {x y : ℝ} (h1 : x^2 - 2 * x + y^4 - 8 * y^3 + 24 * y^2 - 32 * y = -17)
    (h2 : (x - 1)^2 + (y - 2)^4 = 0) :
    x^2 + y^4 - 8 * y^3 = 1 + 16 - 64 := by
  have h3 : (x - 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 2), sq_nonneg ((y - 2) ^ 2)]
  have h4 : (y - 2) ^ 4 = 0 := by 
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 2), sq_nonneg ((y - 2) ^ 2)]
  have hx : x = 1 := by
    have h5 : (x - 1) ^ 2 = 0 := h3
    have h6 : x - 1 = 0 := by 
      nlinarith [pow_eq_zero h5]
    linarith
  have hy : y = 2 := by 
    have h5 : (y - 2) ^ 4 = 0 := h4
    have h6 : (y - 2) ^ 2 = 0 := by 
      have h7 : (y - 2) ^ 4 = ((y - 2) ^ 2) ^ 2 := by ring
      rw [h7] at h5 
      have h8 : (y - 2) ^ 2 = 0 := by 
        nlinarith [sq_nonneg ((y - 2) ^ 2)]
      linarith
    have h7 : y - 2 = 0 := by 
      nlinarith [pow_eq_zero h6]
    linarith
  rw [hx, hy]
  norm_num