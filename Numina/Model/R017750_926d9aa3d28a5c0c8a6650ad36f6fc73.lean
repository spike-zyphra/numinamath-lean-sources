import Mathlib

open Real

theorem calculus_36604 : ⌊(1 + (sqrt 2 + sqrt 3 + sqrt 4) / (sqrt 2 + sqrt 3 + sqrt 6 + sqrt 8 + 4)) ^ 10⌋ = 32 := by

  have h1 : sqrt 4 = 2 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num

  have h2 : sqrt 8 = 2 * sqrt 2 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    <;> ring_nf 
    <;> norm_num

  have h11 : (1 + (sqrt 2 + sqrt 3 + sqrt 4) / (sqrt 2 + sqrt 3 + sqrt 6 + sqrt 8 + 4)) = Real.sqrt 2 := by
    rw [h1, h2]
    have h14 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
      have h23 : Real.sqrt 6 = Real.sqrt (2 * 3: ℝ) := by
        norm_num
      rw [h23]
      rw [Real.sqrt_mul (by norm_num)]
    rw [h14]
    field_simp [(show Real.sqrt 2 ≠ 0 by positivity), (show Real.sqrt 3 ≠ 0 by positivity)]
    nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < (2 : ℝ)), Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < (3 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2 - 1), sq_nonneg (Real.sqrt 3 - 1), mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 3)]
  
  have h43 : (1 + (sqrt 2 + sqrt 3 + sqrt 4) / (sqrt 2 + sqrt 3 + sqrt 6 + sqrt 8 + 4)) ^ 10 = (32 : ℝ) := by
    rw [h11]
    have h51 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
    calc
      Real.sqrt 2 ^ 10 = (Real.sqrt 2 ^ 2) ^ 5 := by ring
      _ = (2) ^ 5 := by rw [h51]
      _ = (32 : ℝ) := by norm_num
  
  rw [h43]
  all_goals norm_num