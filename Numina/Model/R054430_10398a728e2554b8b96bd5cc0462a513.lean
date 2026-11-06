import Mathlib

def x (n : ℕ) := n ^ 4 % 10

theorem number_theory_304296 : ∑ i in Finset.range 2012, x (i + 1) = 6640 := by 
  native_decide