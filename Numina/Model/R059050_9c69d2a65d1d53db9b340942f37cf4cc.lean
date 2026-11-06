import Mathlib

def triangle (a b : ℝ) := 2 * a + b

theorem algebra_176342 (x : ℝ) (h : triangle (triangle 3 2) x = 20) : x = 4 := by
  simp [triangle] at h
  linarith