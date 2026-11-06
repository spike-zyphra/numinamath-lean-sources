import Mathlib

theorem algebra_144474 {N : ℝ} (hN : N ≠ 0) (x : ℝ) (h : (N * x + N) / N - N = x - 100) :
    N = 101 := by
  have eq1 : (N * x + N) / N = x + 1 := by
    have h1 : N ≠ 0 := hN
    field_simp [h1]
    <;> ring
  have eq2 : (N * x + N) / N - N = x + 1 - N := by
    rw [eq1]
  rw [eq2] at h
  linarith