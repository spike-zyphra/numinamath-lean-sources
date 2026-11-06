import Mathlib

theorem algebra_14700 (x y : ℝ) (hy : y = 18) (hxy : x / y = 10 / 4) : x = 45 := by
  rw [hy] at hxy
  field_simp at hxy
  linarith