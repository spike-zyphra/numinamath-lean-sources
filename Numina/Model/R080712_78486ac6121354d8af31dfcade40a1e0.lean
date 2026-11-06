import Mathlib

theorem algebra_1028 (a : ℝ) (ha : a - 1 ≠ 0) (h : (a + 1) / (a - 1) = 3 + 2 * √2) :
    a = √2 := by
  have h1 : a + 1 = (3 + 2 * √2) * (a - 1) := by
    field_simp [ha] at h ⊢
    linarith
  
  have h2 : a + 1 = 3 * (a - 1) + 2 * √2 * (a - 1) := by 
    rw [h1]
    all_goals ring
  
  ring_nf at h2

  -- Using `nlinarith` to solve the remaining algebra to find $a = \sqrt{2}$
  nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num : (0 : ℝ) ≤ 2), mul_self_nonneg (√2 - 1)]