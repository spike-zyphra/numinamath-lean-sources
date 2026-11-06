import Mathlib

def f (x y : ℝ) := 3 * x - y

theorem algebra_8531 (x : ℝ) (hx : f 2 (f 5 x) = 1) : x = 10 := by 
  simp [f] at hx 
  linarith