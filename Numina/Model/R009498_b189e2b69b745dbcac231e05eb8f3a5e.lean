import Mathlib


theorem algebra_9115 {m : ℝ} (hm : m ^ 2 - 2 * m - 3 = 0) : 2 * m ^ 2 - 4 * m = 6 := by
  have h : m^2 - 2 * m = 3 := by
    linarith
  calc 
    2 * m^2 - 4 * m = 2 * (m^2 - 2 * m) := by ring
    _ = 2 * 3 := by rw [h]
    _ = 6 := by norm_num