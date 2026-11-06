import Mathlib

theorem algebra_146035 : (-1 + Complex.I * Real.sqrt 3)^60 = 2^60 := by
  have h1 : (-1 + Complex.I * Real.sqrt 3) ^ 3 = 8 := by
    simp [pow_three, Complex.ext_iff, mul_add, mul_comm, mul_assoc, pow_two, Complex.I_mul_I]
    <;> ring_nf <;> norm_num [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    <;> ring_nf
    <;> norm_num [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), pow_two, pow_succ, Complex.I_mul_I]
    <;> nlinarith
  have h2 : (-1 + Complex.I * Real.sqrt 3) ^ 60 = ((-1 + Complex.I * Real.sqrt 3)^3) ^ 20 := by 
    ring_nf
  rw [h2, h1]
  norm_num
  <;> ring_nf <;> norm_num
  <;> ring_nf
  <;> norm_num