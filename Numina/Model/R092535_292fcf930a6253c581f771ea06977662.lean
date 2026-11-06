import Mathlib

theorem algebra_273815 (N : ℝ) (h : N ≠ 0) (h1 : 50 / 100 * N = 16) :
    75 / 100 * N = 24 := by 
  have hN : N = 32 := by
    linarith
  rw [hN]
  norm_num