import Mathlib

theorem number_theory_159734 : Nat.primeFactorsList 2020 = [2, 2, 5, 101] ∧ Nat.primeFactorsList 2021 = [43, 47] := by 
  constructor
  · -- Check the prime factorization of 2020
    native_decide
  · -- Check the prime factorization of 2021
    native_decide