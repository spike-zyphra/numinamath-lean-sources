import Mathlib

open Finset Real Nat

/- A positive integer is called primer if it has a prime number of distinct prime factors. Find the smallest primer number.-/

-- Here we use Nat.Prime (Nat.primeFactorsList p).dedup.length to check if a number is primer --
theorem Number_Theory_609888: IsLeast {p: ℕ | (1 ≤ p) ∧ Nat.Prime (Nat.primeFactorsList p).dedup.length} 6 := by
  constructor
  . have fac_6: Nat.primeFactorsList 6 = [2,3] := by
      simp only [primeFactorsList]
      norm_num
      simp [Nat.primeFactorsList]
      norm_num
    split_ands
    · omega
    simp [fac_6]
    decide
  . intro n h
    by_contra! k
    simp at h
    rcases h with ⟨g,h⟩
    interval_cases n
    . have fac_1: Nat.primeFactorsList 1 = [] := by
        simp [Nat.primeFactorsList]
      rw [fac_1] at h
      simp at h
      exact Nat.not_prime_zero h
    . have fac_2: Nat.primeFactorsList 2 = [2] := by
        simp [Nat.primeFactorsList]
      rw [fac_2] at h
      simp at h
      exact Nat.not_prime_one h
    . have fac_3: Nat.primeFactorsList 3 = [3] := by
        simp [Nat.primeFactorsList]
        norm_num
      rw [fac_3] at h
      simp at h
      exact Nat.not_prime_one h
    . have fac_4: Nat.primeFactorsList 4 = [2,2] := by
        simp [Nat.primeFactorsList]
        norm_num
      rw [fac_4] at h
      simp at h
      exact Nat.not_prime_one h
    . have fac_5: Nat.primeFactorsList 5 = [5] := by
        simp [Nat.primeFactorsList]
        norm_num
      rw [fac_5] at h
      simp at h
      exact Nat.not_prime_one h
