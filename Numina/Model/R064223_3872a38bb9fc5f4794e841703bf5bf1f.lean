import Mathlib

def f (x y : ℤ) := 2 * x - y ^ 2

theorem algebra_11736 {x : ℤ} (h : f x 5 = 9) : x = 17 := by 
  dsimp [f] at h
  linarith