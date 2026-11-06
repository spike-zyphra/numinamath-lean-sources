import Mathlib

def fact (n : ℕ) := ∏ i ∈ Finset.Icc 1 n, i

theorem number_theory_127998 : (fact 2014 - fact 3) % 10 = 4 := by
  native_decide