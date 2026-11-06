import Mathlib

def S : ℕ → ℕ
| n => (Nat.digits 10 n).sum

theorem number_theory_102770 : ∑ i in Finset.Icc 1 2012, S i = 28077 := by 
  native_decide