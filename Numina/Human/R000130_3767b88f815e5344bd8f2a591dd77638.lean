import Mathlib

/- Determine the highest power of 5 that divides each of the following positive integers:
a) 112250
b) 4860625
c) 235555790
d) 48126953125-/
theorem number_theory_4744 : Nat.factorization 112250 5 = 3 ∧
    Nat.factorization 4860625 5 = 4 ∧
    Nat.factorization 235555790 5 = 1 ∧
    Nat.factorization 48126953125 5 = 9 := by
  -- verify by computation
  native_decide
