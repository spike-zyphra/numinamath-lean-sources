import Mathlib

open Finset Real Nat

/- A positive integer is called primer if it has a prime number of distinct prime factors. Find the smallest primer number.-/

-- Here we use Nat.Prime (Nat.primeFactorsList p).dedup.length to check if a number is primer --
theorem Number_Theory_609888: IsLeast {p: ℕ | (1 ≤ p) ∧ Nat.Prime (Nat.primeFactorsList p).dedup.length} 6 := by
-- We need to prove 6 is the least element of the set of numbers $p$ where $p$ is greater or equal to $1$ and the length of the set of prime factors of $p$ is a prime number.
  constructor
  · -- Show that 6 is indeed in the set.
    constructor
    · norm_num
    · native_decide
  · -- Show that if p is in the set and p < 6, then p must not satisfy the conditions.
    intro p hp
    rcases hp with ⟨hp1, hp2⟩
    by_contra h
    push_neg at h
    interval_cases p <;> norm_num [Nat.primeFactorsList] at hp2 ⊢ <;> try { contradiction }