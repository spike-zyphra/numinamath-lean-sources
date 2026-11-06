import Mathlib

open Real

theorem algebra_145749 : ((1 / (sqrt 3 - sqrt 2) + 2 / (sqrt 8 + sqrt 12)) / (1 / sqrt 3)) = 6 := by
  have h1 : 1 / (sqrt 3 - sqrt 2) = sqrt 3 + sqrt 2 := by
    have h2 : sqrt 3 - sqrt 2 ≠ 0 := by
      have h3 : sqrt 3 > sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      linarith
    field_simp [h2, mul_sub, sub_mul, pow_two, mul_assoc]
    <;> ring_nf <;> norm_num
    <;> ring_nf <;> norm_num
    all_goals norm_num
  have h2 : sqrt 8 = 2 * sqrt 2 := by 
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num 
    <;> ring_nf 
    <;> norm_num
  have h3 : sqrt 12 = 2 * sqrt 3 := by 
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num 
    <;> ring_nf 
    <;> norm_num
  have h4 : 2 / (sqrt 8 + sqrt 12) = sqrt 3 - sqrt 2 := by 
    rw [h2, h3]
    have h5 : (2 * sqrt 2 + 2 * sqrt 3) ≠ 0 := by
      have h6 : sqrt 2 > 0 := Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)
      have h7 : sqrt 3 > 0 := Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)
      nlinarith
    field_simp [h5, mul_add, add_mul, pow_two, mul_comm]
    <;> ring_nf <;> norm_num
    <;> ring_nf <;> norm_num
    all_goals norm_num
  have h5 : sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by linarith)
  have h6 : sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by linarith)
  have h7 : (sqrt 3 + sqrt 2) + (sqrt 3 - sqrt 2) = 2 * sqrt 3 := by ring
  have h8 : (1 / (sqrt 3 - sqrt 2) + 2 / (sqrt 8 + sqrt 12)) = 2 * sqrt 3 := by 
    rw [h1, h4]
    linarith
  rw [h8]
  field_simp [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), h5]
  <;> ring_nf <;> norm_num
  all_goals norm_num