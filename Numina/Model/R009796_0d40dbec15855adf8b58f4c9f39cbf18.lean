import Mathlib

theorem number_theory_162314 : (Nat.primeFactors (1007021035035021007001)) = {7, 11, 13} ∧
    (Nat.primeFactors (1007021035035021007001)).card = 3 ∧
    (Nat.factorization (1007021035035021007001) 7) = 7 ∧
    (Nat.factorization (1007021035035021007001) 11) = 7 ∧
    (Nat.factorization (1007021035035021007001) 13) = 7 := by
  native_decide