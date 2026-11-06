import Mathlib

theorem number_theory_16123 : ∑ i ∈ Finset.Icc 1 (Nat.ofDigits 6 [5, 4]), i = Nat.ofDigits 6 [3, 0, 0, 2] := by 
  native_decide