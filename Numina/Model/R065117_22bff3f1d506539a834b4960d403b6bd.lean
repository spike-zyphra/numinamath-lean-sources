import Mathlib

theorem algebra_144452 {x N : ℤ} (h : N ≠ 0) (h' : (x * N + N) / N - N = x - 2021) :
    N = 2022 := by
  have h1 : (x * N + N) / N = x + 1 := by
    have h2 : (x * N + N) = N * (x + 1) := by ring
    rw [h2]
    field_simp [h]
    <;> ring
  have h2 : (x * N + N) / N - N = x + 1 - N := by
    rw [h1]
  rw [h2] at h'
  omega