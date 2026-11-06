import Mathlib

theorem number_theory_3008 {n : ℕ} (hn : n = 24^4 - 6 * 24^2 + 25) :
    ∃! p, p.Prime ∧ p ∈ Nat.primeFactors n ∧ p ∈ Finset.Icc 100 999 := by 
  rw [hn]
  use 677
  constructor
  · -- First, we verify that 677 is a three-digit prime factor of $n$.
    constructor
    · -- 677 is prime
      norm_num
    constructor
    · -- 677 is in the prime factors of $n$
      native_decide
    · -- 677 is in the range [100, 999]
      native_decide
  · -- Now, we need to prove the uniqueness of 677
    intro p h
    rcases h with ⟨h_prime, h_pf, hp⟩
    rw [Finset.mem_Icc] at hp
    rcases hp with ⟨hp1, hp2⟩
    interval_cases p <;> norm_num [Nat.primeFactors, Nat.primeFactorsList] at h_prime h_pf ⊢
    <;> try { tauto }