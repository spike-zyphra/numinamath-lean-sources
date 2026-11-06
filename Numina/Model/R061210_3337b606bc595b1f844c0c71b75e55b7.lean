import Mathlib

def f (n : ℤ) : ℤ := if Odd n then n ^ 2 else n ^ 2 - 4 * n - 1

theorem algebra_21944 : f (f (f (f (f 4)))) = 1 := by 
  rfl -- Lean can compute this directly