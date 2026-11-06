import Mathlib

theorem number_theory_4743 :
    Nat.factorization 201984 2 = 8 ∧
    Nat.factorization 1423408 2 = 4 ∧
    Nat.factorization 89375744 2 = 10 ∧
    Nat.factorization 41578912246 2 = 1 := by
  native_decide