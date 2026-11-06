import Mathlib

theorem algebra_2141 (n m : ℕ) (h : n + 7 = 2 * m + 3) : (2 * m - n) ^ 2 = 16 := by
  have eq2 : 2 * m - n = 4 := by
    omega 
  calc 
    (2 * m - n) ^ 2 = 4 ^ 2 := by rw [eq2]
    _ = 16 := by norm_num