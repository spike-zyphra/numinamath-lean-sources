import Mathlib

/- Determine the highest power of 2 that divides each of the following positive integers:
a) 201984
b) 1423408
c) 89375744
d) 41578912246-/
theorem number_theory_4743 :
    Nat.factorization 201984 2 = 8 ∧
    Nat.factorization 1423408 2 = 4 ∧
    Nat.factorization 89375744 2 = 10 ∧
    Nat.factorization 41578912246 2 = 1 := by
  -- verify by computation
  native_decide
