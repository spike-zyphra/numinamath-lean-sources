import Mathlib

theorem algebra_2439 (n : ℕ) (h₀ : n > 0) (h : (n + 1) ^ 2 - n ^ 2 = 999) :
    n * (n + 1) = 249500 := by
  have eq3 : (n + 1) ^ 2 - n ^ 2 = 2 * n + 1 := by
    ring_nf
    <;> omega
  rw [eq3] at h
  have hn : n = 499 := by 
    omega
  calc 
    n * (n + 1) = 499 * (499 + 1) := by rw [hn]
    _ = 499 * 500 := by norm_num
    _ = 249500 := by norm_num