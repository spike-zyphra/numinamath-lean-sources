import Mathlib

theorem algebra_276485 (t : ℝ) (ht : t > 0) (h : (1000 * t) ^ 2 = 10 ^ 2 * (t ^ 2 - 1)) :
    t = Real.pi / 200 := by
  nlinarith [Real.pi_pos, sq_nonneg (t), sq_nonneg (t - Real.pi / 200), sq_nonneg (1000 * t), sq_nonneg (10 * t), sq_nonneg ((t : ℝ) ^ 2 * 100 - 100)]