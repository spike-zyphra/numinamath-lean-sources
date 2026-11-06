import Mathlib

def f (n : ℕ) := (∑ i in Finset.Icc 1 n, i) % 10

theorem number_theory_327109 :
    ∑ i in Finset.Icc 1 2004, f i = 7010 := by 
  native_decide