import Mathlib

def f (n : ℕ) := ∑ i in Finset.range n, (i + 1)

theorem number_theory_282713 : f 75 = 2850 := by 
  native_decide