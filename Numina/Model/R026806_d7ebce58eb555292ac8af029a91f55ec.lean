import Mathlib

open Real

theorem inequalities_251 {x y : ℝ} (hx : 1 < x) (hy : 1 < y)
    (h : x * sqrt (y - 1) + y * sqrt (x - 1) ≥ x * y) :
    sqrt (x ^ 3 - x * y + y ^ 3) = 2 * sqrt 3 := by 
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < y - 1 := by linarith
  have h3 : sqrt (x - 1) > 0 := by 
    apply Real.sqrt_pos.mpr
    linarith
  have h4 : sqrt (y - 1) > 0 := by 
    apply Real.sqrt_pos.mpr
    linarith
  have h5 : sqrt (x - 1) ^ 2 = x - 1 := by
    rw [Real.sq_sqrt]
    linarith
  have h6 : sqrt (y - 1) ^ 2 = y - 1 := by 
    rw [Real.sq_sqrt]
    linarith
  have h7 : (sqrt (x - 1) - 1) ^ 2 + (sqrt (y - 1) - 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (sqrt (x - 1) - 1), sq_nonneg (sqrt (y - 1) - 1), 
      h5, h6, sq_nonneg (sqrt (x - 1) * sqrt (y - 1) - 1), 
      Real.sqrt_nonneg (x - 1), Real.sqrt_nonneg (y - 1), 
      mul_nonneg (Real.sqrt_nonneg (x - 1)) (Real.sqrt_nonneg (y - 1)), 
      mul_pos h1 h2, sq_nonneg (x - 2), sq_nonneg (y - 2)
    ]
  have h8 : sqrt (x - 1) - 1 = 0 := by 
    nlinarith [sq_nonneg (sqrt (x - 1) - 1), sq_nonneg (sqrt (y - 1) - 1)]
  have h9 : sqrt (x - 1) = 1 := by linarith
  have hx2 : x = 2 := by 
    have h10 : sqrt (x - 1) ^ 2 = x - 1 := by
      rw [Real.sq_sqrt]
      linarith
    have h12 : sqrt (x - 1) = 1 := h9
    rw [h12] at h10
    linarith 
  have h11 : sqrt (y - 1) - 1 = 0 := by 
    nlinarith [sq_nonneg (sqrt (x - 1) - 1), sq_nonneg (sqrt (y - 1) - 1)]
  have h12 : sqrt (y - 1) = 1 := by linarith 
  have hy2 : y = 2 := by 
    have h13 : sqrt (y - 1) ^ 2 = y - 1 := by 
      rw [Real.sq_sqrt]
      linarith 
    rw [h12] at h13
    linarith 
  have h3' : sqrt (x ^ 3 - x * y + y ^ 3) = sqrt (12 : ℝ) := by 
    rw [hx2, hy2]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
  have h10 : sqrt (x ^ 3 - x * y + y ^ 3) = 2 * sqrt 3 := by 
    rw [h3']
    have h13 : sqrt (12 : ℝ) = 2 * sqrt 3 := by 
      have h55 : sqrt (12 : ℝ) = sqrt (4 * (3 : ℝ)) := by 
        norm_num 
      rw [h55] 
      have h66 : sqrt (4 * (3 : ℝ)) = sqrt (4 : ℝ) * sqrt (3 : ℝ) := by 
        rw [Real.sqrt_mul (by norm_num)] 
      rw [h66] 
      have h88 : sqrt (4 : ℝ) = (2 : ℝ) := by 
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h88] 
      all_goals nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    linarith [h13]
  exact h10