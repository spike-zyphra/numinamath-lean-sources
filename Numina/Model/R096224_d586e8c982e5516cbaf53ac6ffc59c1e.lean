import Mathlib

theorem algebra_33936 (father son : ℕ) (hn : father = 42) (h : son = 14) :
    ∃ n, father + n = 2 * (son + n) := by
  use 14
  calc
    father + 14 = 42 + 14 := by rw [hn]
    _ = 56 := by norm_num
    _ = 2 * (14 + 14) := by norm_num
    _ = 2 * (son + 14) := by rw [h]