import Mathlib

theorem number_theory_97714 : (Nat.digits 10 (∑ i ∈ Finset.range 321, (10^(i + 1) - 1))).sum = 342 := by
  native_decide