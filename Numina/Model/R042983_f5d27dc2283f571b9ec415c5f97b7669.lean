import Mathlib

open Polynomial

theorem algebra_11156 {P : ℤ[X]} (hP : P = X ^ 3 - 3 * X ^ 2 + 3 * X - 3) : Polynomial.aeval ((2 : ℝ) ^ ((1 : ℝ) / 3) + 1) P = 0 := by 
  rw [hP]
  simp [Polynomial.aeval, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  have h1 : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (2 : ℝ) := by 
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num 
    all_goals linarith 
  have eq3 : (2 ^ (3⁻¹ : ℝ) : ℝ) = (2 : ℝ) ^ ((1 : ℝ) / 3) := by 
    norm_num
  rw [eq3]
  have h3 : ((2 : ℝ) ^ ((1 : ℝ) / 3) + 1 : ℝ) ^ 3 = 3 + 3 * ((2 : ℝ) ^ ((1 : ℝ) / 3)) + 3 * ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 := by 
    have h1' : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (2 : ℝ) := h1
    have h4 : ((2 : ℝ) ^ ((1 : ℝ) / 3) + 1 : ℝ) ^ 3 = ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 + 3 * ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 + 3 * ((2 : ℝ) ^ ((1 : ℝ) / 3)) + 1 := by 
      ring 
    rw [h4, h1']
    all_goals linarith 
  have h4 : ((2 : ℝ) ^ ((1 : ℝ) / 3) + 1 : ℝ) ^ 2 = ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 + 2 * ((2 : ℝ) ^ ((1 : ℝ) / 3)) + 1 := by 
    ring 
  nlinarith [sq_nonneg ((2 : ℝ) ^ ((1 : ℝ) / 3) - 1), sq_nonneg ((2 : ℝ) ^ ((1 : ℝ) / 3)), h1, sq_nonneg ((2 : ℝ) ^ ((1 : ℝ) / 3) + 1), Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (1 / 3)]