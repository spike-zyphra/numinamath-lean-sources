import Mathlib

/-- (1) Find the prime factorization of 692921. -/
theorem number_theory_4607_1 :
  --The prime factorization of 692921 is $23 * 47 * 641$.
  Nat.factorization 692921 23 = 1 ∧ Nat.factorization 692921 47 = 1 ∧ Nat.factorization 692921 641 = 1
    := by native_decide

/-- (2) Find the prime factorization of 1468789. -/
theorem number_theory_4607_2 :
  --The prime factorization of 1468789 is $7 * 37 * 53 * 107$.
  Nat.factorization 1468789 7 = 1 ∧ Nat.factorization 1468789 37 = 1 ∧ Nat.factorization 1468789 53 = 1
    ∧ Nat.factorization 1468789 107 = 1
    := by native_decide

/-- (3) Find the prime factorization of 55608079. -/
theorem number_theory_4607_3 :
  -- The prime factorization of 55608079 is $19^2 * 31 * 4969$. 
  Nat.factorization 55608079 19 = 2 ∧ Nat.factorization 55608079 31 = 1 ∧ Nat.factorization 55608079 4969 = 1
    := by native_decide
