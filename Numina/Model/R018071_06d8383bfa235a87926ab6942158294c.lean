import Mathlib

theorem algebra_4356 {p q r : ℝ} (h₀ : p > 0) (h₁ : q > 0) (h₂ : r > 0)
    (h₃ : p + q = 10) (h₄ : p * q = r ^ 2 - 12 * r + 61) :
    (1 / 2) * p * q * Real.sin (Real.arccos ((p ^ 2 + q ^ 2 - r ^ 2) / (2 * p * q))) = 12 := by

  have h5 : q = 10 - p := by linarith
  rw [h5] at h₄
  have h6 : r = 6 := by
    nlinarith [sq_nonneg (p - 5), sq_nonneg (r - 6), sq_nonneg ((10 - p) - 5)]
  have h7 : p = 5 := by
    rw [h6] at h₄
    nlinarith [sq_nonneg (p - 5)]
  have h8 : q = 5 := by
    linarith
  have hp2 : p ^ 2 + q ^ 2 - r ^ 2 = 14 := by 
    rw [h7, h8, h6]
    norm_num
  have h9 : (p ^ 2 + q ^ 2 - r ^ 2) / (2 * p * q) = 7 / 25 := by
    have h10 : p * q = 25 := by
      nlinarith [h7, h8]
    have h11 : 2 * p * q = 50 := by
      nlinarith
    rw [h11]
    rw [hp2]
    all_goals norm_num
  have h13 : Real.sin (Real.arccos ((p ^ 2 + q ^ 2 - r ^ 2) / (2 * p * q))) = 24 / 25 := by
    rw [h9]
    have h14 : Real.sin (Real.arccos (7 / 25 : ℝ)) = Real.sqrt (1 - (7 / 25 : ℝ) ^ 2) := by 
      rw [Real.sin_arccos]
    rw [h14]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  rw [h13]
  rw [h7, h8]
  norm_num