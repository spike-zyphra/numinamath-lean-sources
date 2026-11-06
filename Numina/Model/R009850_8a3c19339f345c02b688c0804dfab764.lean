import Mathlib

theorem algebra_14820 {n : ℕ} (hn : n > 0) (h : (n - 2) * 180 = n * (180 - 120)) :
    n * 5 = 15 := by
  have h1 : n = 3 := by
    omega
  calc
    n * 5 = 3 * 5 := by rw [h1]
    _ = 15 := by norm_num