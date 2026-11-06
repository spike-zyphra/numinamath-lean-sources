import Mathlib

theorem number_theory_167077 : (∑ i ∈ Finset.Icc 1 100, Nat.factorial i) % 1000 = 313 := by native_decide