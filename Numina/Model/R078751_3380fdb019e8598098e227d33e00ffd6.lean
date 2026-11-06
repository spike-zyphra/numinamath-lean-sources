import Mathlib

def M : ℕ := ∑ i ∈ Finset.range 2007, 10 ^ i

theorem number_theory_175123 : (Nat.digits 10 (2007 * M)).sum = 18063 := by 
  native_decide