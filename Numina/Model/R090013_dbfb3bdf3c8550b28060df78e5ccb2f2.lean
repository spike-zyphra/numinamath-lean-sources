import Mathlib

theorem algebra_95216 {x y : ℝ} (hy : y ≠ 0) (h : x = (3 / 4) * y * (2 / 3)) :
    x / y = 1 / 2 := by
  have h1 : x = (1 / 2) * y := by
    linarith
  have h2 : x / y = (1 / 2) := by
    field_simp [hy] at *
    linarith
  linarith