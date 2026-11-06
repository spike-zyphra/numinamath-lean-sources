import Mathlib

theorem algebra_211463 {a b c : ℝ} (h : a + b + c = 1) :
    a + b * c = (a + b) * (a + c) := by
  have hc : c = 1 - a - b := by linarith
  rw [hc]
  ring