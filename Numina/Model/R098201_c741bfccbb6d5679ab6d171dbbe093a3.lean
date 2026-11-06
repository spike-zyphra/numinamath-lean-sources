import Mathlib

def R : ℕ → ℕ
| k => ∑ i ∈ Finset.range k, 10 ^ i

theorem number_theory_274599 : (Nat.digits 10 (R 24 / R 4)).count 0 = 15 := by 
  native_decide