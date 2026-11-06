import Mathlib

def f (n : ℤ) : ℤ := if Odd n then n ^ 2 + 1 else n ^ 2 - 3 * n + 1

theorem algebra_20299 : f (f (f (f (f (f 2))))) = 2 := by
  rfl