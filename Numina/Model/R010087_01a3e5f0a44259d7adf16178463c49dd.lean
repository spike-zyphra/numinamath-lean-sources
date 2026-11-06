import Mathlib

theorem number_theory_15692 : ((∑ i ∈ Finset.range 9, (Nat.factorial (i + 1) + (i + 1))) % 10 = 8) := by 
  native_decide