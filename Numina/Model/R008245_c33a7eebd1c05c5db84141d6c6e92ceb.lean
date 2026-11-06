import Mathlib

theorem algebra_14380 {a : ℝ} (h : (4, -8) ∈ { (x, y) | a * x + (a + 1) * y = a + 2 }) :
    a = -2 := by
  dsimp at h
  linarith