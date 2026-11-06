import Mathlib

open Nat

def prod_of_primes (n : ℕ) := ∏ p in n.primesBelow, p

lemma lemma_product_of_odd_is_odd (s : Finset ℕ) (hs : ∀ n ∈ s, Odd n) : Odd (∏ i ∈ s, i) := by
  revert hs
  refine Finset.induction_on s ?_ ?_
  . simp
  . intro n s hn ih h
    rw [Finset.prod_insert hn, Nat.odd_mul]
    constructor
    . exact h n (by simp)
    . apply ih
      intro n hn
      apply h n
      simp
      tauto

theorem lemma_four_not_dvd_primes (s : Finset ℕ) (hs : ∀ n ∈ s, n.Prime) :
    ¬4 ∣ ∏ i ∈ s, i := by
  by_contra! h
  by_cases 2 ∈ s
  . have : s = insert 2 (s.filter (2 < ·)) := by
      apply Finset.ext
      intro a
      constructor <;> simp
      . intro ha
        by_cases a = 2
        . tauto
        . have : 2 < a := by
            specialize hs a ha
            have := Nat.Prime.two_le hs
            omega
          tauto
      . rintro (ha|ha)
        . subst a
          assumption
        . tauto
    rw [this, Finset.prod_insert (by simp)] at h
    have := lemma_product_of_odd_is_odd (s.filter (2 < ·)) ?odd
    case odd =>
      intro n hn
      simp at hn
      obtain ⟨hn1, hn2⟩ := hn
      specialize hs n hn1
      exact Nat.Prime.odd_of_ne_two hs (by omega)
    simp [Odd] at this
    omega
  . have := lemma_product_of_odd_is_odd s ?odd
    case odd =>
      intro n hn
      specialize hs n hn
      apply Nat.Prime.odd_of_ne_two hs
      by_contra!
      subst n
      contradiction
    simp [Odd] at this
    omega

/- 8.7. For a natural number $n(n>3)$, we use “$n$ ?" to denote the product of all prime numbers less than $n$. Solve the equation
$$
n ?=2 n+16
$$ -/
theorem number_theory_317482 {n : ℕ} (hn : n > 3) :
    prod_of_primes n = 2 * n + 16 ↔ n = 7 := by
  constructor
  . intros h
    -- n is odd
    have hodd : Odd n := by
      by_contra! h1
      have : 4 ∣ 2 * n + 16 := by
        simp at h1
        obtain ⟨r, hr⟩ := h1
        omega
      rw [←h] at this
      simp [prod_of_primes] at this
      -- since n? cannot be divisible by 4
      apply lemma_four_not_dvd_primes n.primesBelow ?_ this
      simp [primesBelow]
    -- We prove n ≤ 9 by contradiction.
    have : n ≤ 9 := by
      -- if n > 9
      by_contra! h1
      -- the n - 8 is odd
      have h2 : Odd (n - 8) := by
        obtain ⟨k, hk⟩ := hodd
        use k - 4
        omega
      -- and n - 8 has an odd prime factor p
      obtain ⟨p, pprime, pdvd⟩ := Nat.exists_prime_and_dvd (n := n - 8) (by omega)
      have podd : Odd p := by
        apply Nat.Prime.odd_of_ne_two pprime
        by_contra!
        subst p
        simp [Odd] at hodd
        omega
      -- since p ≤ n - 8 < n, p | n?
      have h3 : p ∣ prod_of_primes n := by
        simp [prod_of_primes]
        apply Finset.dvd_prod_of_mem
        simp [primesBelow]
        constructor
        . have := Nat.le_of_dvd (by omega) pdvd
          omega
        . assumption
      -- thus p | 2n + 16
      rw [h] at h3
      -- since p is odd, p | n + 8
      have h4 : p ∣ n + 8 := by
        apply Nat.Coprime.dvd_of_dvd_mul_left (m := 2)
        . simp
          assumption
        . ring_nf
          ring_nf at h3
          assumption
      -- therefore, p | 16, which leads to a contradiction
      have h5 := Nat.dvd_sub (by omega) h4 pdvd
      have : n + 8 - (n - 8) = 16 := by omega
      rw [this] at h5
      have := Nat.le_of_dvd (by omega) h5
      interval_cases p <;> try simp [Odd] at hodd; omega
      simp [Nat.Prime] at pprime
    -- and we try 5 and 9 which is not the solution
    interval_cases h1 : n <;> try simp [Odd] at hodd; omega
    all_goals
    have : prod_of_primes n ≠ 2 * n + 16 := by
      subst n
      decide
    subst n
    contradiction
  . intros h
    subst n
    decide
