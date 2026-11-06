import Mathlib

open Nat


theorem number_theory_636029 (n : ℕ) (hn : n > 0) (a b : ℕ) (A : ℕ) (hA : A = 2 ^ a * 5 ^ b) :
  Nat.gcd (Nat.factorial n) A = 2 ^ (min (Nat.factorization (Nat.factorial n) 2) a) * 5 ^ (min (Nat.factorization (Nat.factorial n) 5) b) := by 
  have neq1 : (Nat.factorial n) ≠ 0 := by 
    exact factorial_ne_zero n
  have aneq : A ≠ 0 := by 
    rw [hA]
    positivity
  obtain h1 := factorization_gcd neq1 aneq
  refine Nat.eq_of_factorization_eq ?_ ?_ ?_
  · exact gcd_ne_zero_left neq1
  · positivity
  intro p 
  rw [h1]
  simp
  by_cases peq2 : p = 2 
  · rw [peq2]
    have eq0 : (Nat.factorization 5) 2 = 0 := by 
      refine factorization_eq_zero_of_not_dvd ?_
      norm_num
    have eq1 : (Nat.factorization 2) 2 = 1 := by 
      refine Prime.factorization_self ?_
      norm_num
    simp [eq0, eq1]
    have eq2 : A.factorization 2 = a := by
      rw [hA]
      simp
      simp [eq0, eq1]
    rw [eq2]
  by_cases peq5 : p = 5 
  · rw [peq5]
    have eq0 : (Nat.factorization 2) 5 = 0 := by 
      refine factorization_eq_zero_of_not_dvd ?_
      norm_num
    have eq1 : (Nat.factorization 5) 5 = 1 := by 
      refine Prime.factorization_self ?_
      norm_num
    simp [eq0, eq1]
    have eq2 : A.factorization 5 = b := by
      rw [hA]
      simp
      simp [eq0, eq1]
    rw [eq2]
  · -- p ≠ 2, p ≠ 5
    by_cases primep : Nat.Prime p
    · have aux1 : A.factorization p = 0 := by 
        by_contra hc
        have ge1 : A.factorization p ≥ 1 := by omega
        have dvd1 : p ∣ A := by 
          exact dvd_of_factorization_pos hc
        rw [hA] at dvd1
        have pdvd_or : p ∣ 2 ^ a ∨ p ∣ 5 ^ b := by
          exact (Nat.Prime.dvd_mul primep).mp dvd1
        obtain pdvd1 | pdvd2 := pdvd_or
        · -- the case p ∣ 2 ^ 1
          have pdvd_two : p ∣ 2 := by 
            exact Nat.Prime.dvd_of_dvd_pow primep pdvd1
          have prime2 : Nat.Prime 2 := by 
            norm_num
          obtain heq := (Nat.prime_dvd_prime_iff_eq primep prime2).mp pdvd_two
          exact peq2 heq
        · -- the case p ∣ 5 ^ b 
          have pdvd_two : p ∣ 5 := by 
            exact Nat.Prime.dvd_of_dvd_pow primep pdvd2
          have prime2 : Nat.Prime 5 := by 
            norm_num
          obtain heq := (Nat.prime_dvd_prime_iff_eq primep prime2).mp pdvd_two
          exact peq5 heq
      rw [aux1]
      simp
      have aux2 : (Nat.factorization 2) p = 0 := by
        refine factorization_eq_zero_of_not_dvd ?_
        by_contra hc
        have prime2 : Nat.Prime 2 := by 
          norm_num
        obtain heq := (Nat.prime_dvd_prime_iff_eq primep prime2).mp hc
        exact peq2 heq
      have aux3 : (Nat.factorization 5) p = 0 := by
        refine factorization_eq_zero_of_not_dvd ?_
        by_contra hc
        have prime5 : Nat.Prime 5 := by 
          norm_num
        obtain heq := (Nat.prime_dvd_prime_iff_eq primep prime5).mp hc
        exact peq5 heq
      simp [aux2, aux3]
    · -- the case p is not a prime
      have aux1 : A.factorization p = 0 := by 
        exact factorization_eq_zero_of_non_prime A primep
      rw [aux1]
      simp
      have aux2 : (Nat.factorization 2) p = 0 := by
        exact factorization_eq_zero_of_non_prime 2 primep
      have aux3 : (Nat.factorization 5) p = 0 := by
        exact factorization_eq_zero_of_non_prime 5 primep
      simp [aux2, aux3]
