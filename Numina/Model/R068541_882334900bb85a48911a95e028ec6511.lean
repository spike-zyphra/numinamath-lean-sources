import Mathlib

def a (n : ℕ) := (∑ i in Finset.Icc 1 n, i) % 10

theorem number_theory_212282 : ∑ i in Finset.Icc 1 1992, a i = 6984 := by
  native_decide