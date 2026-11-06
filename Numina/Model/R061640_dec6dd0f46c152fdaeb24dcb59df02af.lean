import Mathlib

def f (a b : ℝ) := 2 * a - b ^ 2

theorem algebra_4879 {a : ℝ} (ha : f a 5 = 9) : a = 17 := by 
  dsimp [f] at ha
  linarith