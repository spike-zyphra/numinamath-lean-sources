import Mathlib

theorem algebra_21903 (x : ℝ) (hx : x ≠ 0) (h : 192 * x ^ 2 - 16 = 0) : 1 / x ^ 4 = 144 := by 
  have h1 : x ^ 2 = 1 / 12 := by
    nlinarith
  have h2 : x ^ 4 = 1 / 144 := by 
    calc
      x ^ 4 = (x ^ 2) ^ 2 := by ring
      _ = (1 / 12) ^ 2 := by rw [h1]
      _ = 1 / 144 := by norm_num
  rw [h2]
  norm_num