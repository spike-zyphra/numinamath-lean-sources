import Mathlib

theorem algebra_7989 (x : ℝ) (hx : 0 ≤ x + 8) (h : Real.sqrt (x + 8) = x + 2) : x = 1 := by
  have h1 : Real.sqrt (x + 8) ≥ 0 := by
    apply Real.sqrt_nonneg
  have h2 : (x + 2) ≥ 0 := by
    nlinarith [Real.sqrt_nonneg (x + 8), h]
  have h3 : (Real.sqrt (x + 8)) ^ 2 = (x + 2) ^ 2 := by
    rw [h]
  have h4 : (Real.sqrt (x + 8)) ^ 2 = x + 8 := by
    rw [Real.sq_sqrt]
    linarith
  rw [h4] at h3
  have h5 : (x + 2) ^ 2 = x ^ 2 + 4 * x + 4 := by
    ring
  rw [h5] at h3
  have h6 : x ^ 2 + 3 * x - 4 = 0 := by
    nlinarith
  have h7 : (x - 1) * (x + 4) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h7) with h8 h9
  · -- Case where $(x - 1) = 0$
    linarith
  · -- Case where $(x + 4) = 0$
    have h10 : x = -4 := by linarith
    have h11 : Real.sqrt ( (-4 : ℝ) + 8 ) = 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h10] at h
    have h12 : Real.sqrt ( (-4 : ℝ) + 8 ) = -4 + 2 := by
      linarith [h]
    rw [h11] at h12
    linarith