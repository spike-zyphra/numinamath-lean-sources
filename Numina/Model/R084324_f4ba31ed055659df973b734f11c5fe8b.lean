import Mathlib

theorem algebra_11157 {n : ℕ} (hn : n = 10) :
    (n * (n - 3)) / 2 = 35 := by
  calc
    (n * (n - 3)) / 2 = (10 * (10 - 3)) / 2 := by rw [hn]
    _ = (10 * 7) / 2 := by norm_num
    _ = 70 / 2 := by norm_num
    _ = 35 := by norm_num