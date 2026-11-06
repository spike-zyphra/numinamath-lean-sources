import Mathlib

theorem algebra_231863 {a b : ℝ} (ha : a + b = 7) (hb : a - b = 2) : a * b = 11 + 1 / 4 := by 
  have h1 : a = 9 / 2 := by
    linarith
  have h2 : b = 5 / 2 := by
    linarith
  rw [h1, h2]
  norm_num