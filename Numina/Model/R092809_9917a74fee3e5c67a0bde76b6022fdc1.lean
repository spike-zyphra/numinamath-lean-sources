import Mathlib

def solution := 1994

theorem number_theory_1544 : ∑ i in Finset.range solution, (Nat.digits 10 (i + 1)).length = 6869 := by 
  native_decide