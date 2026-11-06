import Mathlib

theorem algebra_320126 {m : ℝ} (hm : m ≠ -3) (h : m = -1 / 6) :
    (21 - 5 * m) / (m ^ 2 - 9) - m / (m ^ 2 - 9) / (m / (m + 3)) - (m - 3) / (m + 3) = -1 := by 
  rw [h]
  norm_num
  <;> linarith