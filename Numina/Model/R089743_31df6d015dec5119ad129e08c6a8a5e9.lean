import Mathlib

def E : ℕ → ℕ
| n => ∑ i ∈ Finset.range (Nat.digits 10 n).length, if Even (Nat.digits 10 n)[i]! then (Nat.digits 10 n)[i]! else 0

theorem number_theory_98468 : ∑ i ∈ Finset.range 100, E (i + 1) = 400 := by 
  native_decide