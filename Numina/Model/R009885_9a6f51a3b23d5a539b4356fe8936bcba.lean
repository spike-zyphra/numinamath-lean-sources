import Mathlib

theorem algebra_14639 {n : ℕ} (hn : Odd n) (h : n + 2 = 3 * n) : n + (n + 2) = 4 := by 
  have eq1 : n = 1 := by 
    omega 
  calc 
    n + (n + 2) = 1 + (1 + 2) := by rw [eq1] 
    _ = 1 + 3 := by norm_num 
    _ = 4 := by norm_num