import Mathlib

def f (n : ℕ) := n * (n + 1)

theorem algebra_205990 :
    f 6 = 42 ∧ f 1994 = 1994 * 1995 := by 
  constructor
  · rfl -- prove f 6 = 42
  · rfl -- prove f 1994 = 1994 * 1995