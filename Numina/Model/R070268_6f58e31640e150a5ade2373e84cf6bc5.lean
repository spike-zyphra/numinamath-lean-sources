import Mathlib

theorem number_theory_6195 : (Nat.digits 10 (∑ i ∈ Finset.Icc 1 100, Nat.ofDigits 10 (List.replicate i 1))).sum = 415 := by
  native_decide