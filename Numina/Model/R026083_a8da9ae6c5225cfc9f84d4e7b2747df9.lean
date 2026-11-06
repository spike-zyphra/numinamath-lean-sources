import Mathlib

open Real

theorem algebra_155927 (f : ℝ → ℝ) (hf : f = fun x => sqrt (3 * x ^ 2 + 1)) :
    deriv f 1 * (1.02 - 1) + f 1 = 2.03 := by
  have h1 : f 1 = sqrt (3 * (1:ℝ) ^ 2 + 1) := by
    rw [hf]
  have h2 : f 1 = 2 := by
    rw [h1]
    have h4 : sqrt (3 * (1:ℝ) ^ 2 + 1) = 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    linarith [h4]
  have h3 : deriv f 1 = (3 * (1:ℝ)) / (sqrt (3 * (1:ℝ) ^ 2 + 1)) := by
    rw [hf]
    simp [deriv_sqrt, deriv_add, deriv_const, deriv_mul, mul_comm]
    <;> field_simp [Real.sqrt_eq_iff_sq_eq, h1]
    <;> norm_num
    <;> ring_nf <;> norm_num
  have h4 : sqrt (3 * (1:ℝ) ^ 2 + 1) = (2 : ℝ) := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  rw [h2, h3, h4]
  norm_num
  <;> ring_nf <;> norm_num