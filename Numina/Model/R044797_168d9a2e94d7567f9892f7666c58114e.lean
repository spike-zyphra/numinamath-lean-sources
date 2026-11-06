import Mathlib

theorem algebra_148070 (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 1) (hz : z ≥ 2)
    (h : 4 * (Real.sqrt x + Real.sqrt (y - 1) + Real.sqrt (z - 2)) = x + y + z + 9) :
    x * y * z = 120 := by

  have h1 : Real.sqrt x ≥ 0 := by
    apply Real.sqrt_nonneg

  have h2 : Real.sqrt (y - 1) ≥ 0 := by
    apply Real.sqrt_nonneg

  have h3 : Real.sqrt (z - 2) ≥ 0 := by
    apply Real.sqrt_nonneg

  have h4 : (Real.sqrt x) ^ 2 = x := by
    rw [Real.sq_sqrt]
    linarith

  have h5 : (Real.sqrt (y - 1)) ^ 2 = y - 1 := by
    rw [Real.sq_sqrt]
    linarith

  have h6 : (Real.sqrt (z - 2)) ^ 2 = z - 2 := by
    rw [Real.sq_sqrt]
    linarith

  have h_eq : (Real.sqrt x - 2) ^ 2 + (Real.sqrt (y - 1) - 2) ^ 2 + (Real.sqrt (z - 2) - 2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (Real.sqrt x - 2), sq_nonneg (Real.sqrt (y - 1) - 2), sq_nonneg (Real.sqrt (z - 2) - 2), Real.sqrt_nonneg x, Real.sqrt_nonneg (y - 1), Real.sqrt_nonneg (z - 2), h4, h5, h6]

  have h7 : Real.sqrt x - 2 = 0 := by
    nlinarith [sq_nonneg (Real.sqrt x - 2), sq_nonneg (Real.sqrt (y - 1) - 2), sq_nonneg (Real.sqrt (z - 2) - 2), h_eq]

  have h8 : Real.sqrt (y - 1) - 2 = 0 := by
    nlinarith [sq_nonneg (Real.sqrt x - 2), sq_nonneg (Real.sqrt (y - 1) - 2), sq_nonneg (Real.sqrt (z - 2) - 2), h_eq]

  have h9 : Real.sqrt (z - 2) - 2 = 0 := by
    nlinarith [sq_nonneg (Real.sqrt x - 2), sq_nonneg (Real.sqrt (y - 1) - 2), sq_nonneg (Real.sqrt (z - 2) - 2), h_eq]

  have hx2 : x = 4 := by
    have h10 : Real.sqrt x = 2 := by
      linarith [h7]
    have h11 : x = (Real.sqrt x) ^ 2 := by
      rw [Real.sq_sqrt]
      linarith
    rw [h10] at h11
    nlinarith

  have hy2 : y = 5 := by
    have h12 : Real.sqrt (y - 1) = 2 := by
      linarith [h8]
    have h13 : y - 1 = (Real.sqrt (y - 1)) ^ 2 := by
      rw [Real.sq_sqrt]
      linarith
    rw [h12] at h13
    linarith

  have hz2 : z = 6 := by
    have h14 : Real.sqrt (z - 2) = 2 := by
      linarith [h9]
    have h15 : z - 2 = (Real.sqrt (z - 2)) ^ 2 := by
      rw [Real.sq_sqrt]
      linarith
    rw [h14] at h15
    linarith

  rw [hx2, hy2, hz2]
  all_goals norm_num