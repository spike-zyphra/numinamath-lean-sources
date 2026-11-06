import Mathlib

theorem algebra_144474 {N : ℝ} (hN : N ≠ 0) (x : ℝ) (h : (N * x + N) / N - N = x - 100) :
    N = 101 := by
  have h1 : (N * x + N) / N = x + 1 := by
    rw [show N * x + N = N * (x + 1) by ring]
    simp [hN]
  have h2 : (N * x + N) / N - N = x + 1 - N := by rw [h1]
  rw [h2] at h
  have : 1 - N = -100 := by linarith
  linarith