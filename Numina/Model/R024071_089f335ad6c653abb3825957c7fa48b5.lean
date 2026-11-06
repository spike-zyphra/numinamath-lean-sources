import Mathlib

def f (x y : ℝ) := (x - y)^2

theorem algebra_97547 : f (f x y) (f y x) = 0 := by
  simp [f]
  <;> nlinarith [sq_nonneg (x - y), sq_nonneg (y - x)]