import Mathlib

theorem algebra_317620 {a b : ℝ} (h : 0 ≤ 2 * a - 1) (h' : |b + 1| = -Real.sqrt (2 * a - 1)) :
    a ^ (-2 : ℤ) + b ^ (-1987 : ℤ) = 3 := by
  have h1 : Real.sqrt (2 * a - 1) ≥ 0 := by 
    apply Real.sqrt_nonneg
  have h2 : |b + 1| ≥ 0 := by 
    apply abs_nonneg
  have h3 : Real.sqrt (2 * a - 1) = 0 := by
    have h3' : Real.sqrt (2 * a - 1) ≤ 0 := by
      linarith [abs_nonneg (b + 1), h1, h']
    linarith [h1, h3']
  have h4 : |b + 1| = 0 := by 
    linarith [h', h3]
  have ha : a = 1 / 2 := by 
    have h5 : 2 * a - 1 = 0 := by 
      rw [Real.sqrt_eq_zero (by linarith)] at h3
      linarith
    linarith
  have hb : b = -1 := by 
    rw [abs_eq_zero] at h4
    linarith
  rw [ha, hb]
  norm_num
  all_goals try norm_num