import Mathlib

theorem number_theory_5174 :
  (Nat.digits 10 (2002 * ∑ i ∈ Finset.range 2000, 10^i)).sum = 8000 := by
  native_decide