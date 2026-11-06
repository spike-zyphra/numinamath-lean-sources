import Mathlib

open Real

theorem algebra_2350 {P : ℝ} (hP : P = sqrt (1988 * 1989 * 1990 * 1991 + 1) - (1989 ^ 2)) : P = 1988 := by
  have h : sqrt (1988 * 1989 * 1990 * 1991 + 1 : ℝ) = (1989 ^ 2 + 1989 - 1 : ℝ) := by
    have h_eq : (1988 * 1989 * 1990 * 1991 + 1 : ℝ) = (1989 ^ 2 + 1989 - 1 : ℝ) ^ 2 := by norm_num
    rw [h_eq]
    rw [Real.sqrt_sq (by norm_num)]
  rw [h] at hP
  linarith