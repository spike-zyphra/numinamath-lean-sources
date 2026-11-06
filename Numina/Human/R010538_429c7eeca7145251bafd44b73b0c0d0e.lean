import Mathlib

/- Find the units digit of the sum, $$ 1! + 2! + 3! + \cdots + 2006!. $$ -/
theorem number_theory_17052 : (∑ i in Finset.Icc 1 2006, Nat.factorial i) % 10 = 3 := by
  native_decide
