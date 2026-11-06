import Mathlib

theorem algebra_306672 {a b c : ℝ} (ha : a = 2 * b + Real.sqrt 2)
    (h : a * b + (Real.sqrt 3 / 2) * c ^ 2 + (1 / 4) = 0) :
    b * c / a = 0 := by
  have eq1 : a = 2 * b + Real.sqrt 2 := ha
  rw [eq1] at h
  have h1 : 2 * (b + Real.sqrt 2 / 4) ^ 2 + (Real.sqrt 3 / 2) * c ^ 2 = 0 := by
    nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, 
              Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
              Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num),
              sq_nonneg (b + Real.sqrt 2 / 4), sq_nonneg c]
  have h2 : (b + Real.sqrt 2 / 4) ^ 2 = 0 := by
    nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, 
              Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
              Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num),
              sq_nonneg (b + Real.sqrt 2 / 4), sq_nonneg c]
  have h3 : c ^ 2 = 0 := by 
    nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, 
              Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
              Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num),
              sq_nonneg (b + Real.sqrt 2 / 4), sq_nonneg c]
  have hc : c = 0 := by
    nlinarith [sq_nonneg c]
  have hbc : b * c = 0 := by
    rw [hc]
    norm_num
  have ha' : a = Real.sqrt 2 / 2 := by
    rw [ha]
    have hb : b = -Real.sqrt 2 / 4 := by
      nlinarith [Real.sqrt_nonneg 2, h2]
    rw [hb]
    ring_nf
  have ha_ne_zero : a ≠ 0 := by
    rw [ha']
    have h1 : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0)
    linarith
  rw [show b * c / a = (b * c) / a by simp]
  rw [hbc]
  norm_num [ha_ne_zero]