import Mathlib

theorem number_theory_8428 : ((20).factorial).divisors.card = 41040 := by
  let n := (20).factorial
  have h1 : n.divisors.card = ∏ x ∈ n.primeFactors, (n.factorization x + 1) := by 
    apply Nat.card_divisors
    exact Nat.factorial_ne_zero 20

  have h2 : n.primeFactors = {2,3,5,7,11,13,17,19} := by native_decide

  have h3 : n.factorization 2 = 18 := by native_decide
  have h4 : n.factorization 3 = 8 := by native_decide
  have h5 : n.factorization 5 = 4 := by native_decide
  have h6 : n.factorization 7 = 2 := by native_decide
  have h7 : n.factorization 11 = 1 := by native_decide
  have h8 : n.factorization 13 = 1 := by native_decide
  have h9 : n.factorization 17 = 1 := by native_decide
  have h10 : n.factorization 19 = 1 := by native_decide

  rw [h1]
  rw [h2]
  simp [Finset.prod_insert, Finset.prod_singleton, h3, h4, h5, h6, h7, h8, h9, h10]
  all_goals native_decide