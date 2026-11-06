import Mathlib

def f (x : ℤ) : ℤ := x ^ 2
def Δf (x : ℤ) : ℤ := f (x + 1) - f x

theorem algebra_8033 {a b : ℤ} : Δf (a + b) = 2 * a + 2 * b + 1 := by 
  unfold Δf f
  ring