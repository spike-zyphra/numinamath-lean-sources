import Mathlib
/- What is the smallest positive integer $n$ which cannot be written in any of the following forms?

- $n=1+2+\cdots+k$ for a positive integer $k$.
- $n=p^{k}$ for a prime number $p$ and integer $k$.
- $n=p+1$ for a prime number $p$.
- $n=p q$ for some distinct prime numbers $p$ and $q$ -/
theorem number_theory_609323 : IsLeast {n : ℕ | n > 0 ∧ (∀ k > 0, (n ≠ ∑ i in Finset.range (k + 1), i)) ∧ (∀ k p : ℕ, p.Prime → n ≠ p ^ k) ∧ (∀ p : ℕ, p.Prime → n ≠ p + 1) ∧ (∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → n ≠ p * q)} 40:= by
  constructor
  .
    -- Establish that 2 and 5 are prime numbers
    have g1 : Nat.Prime 2:= by norm_num
    have g2 : Nat.Prime 5:= by norm_num
    refine ⟨(by omega), ?_, ?_, ?_, ?_⟩
    .
      -- Prove that 40 cannot be written as a sum of consecutive integers from 1 to k
      intro k hk
      by_contra H
      -- If 40 = 1+2+...+k, then k must be greater than 8
      have hk1 : k > 8:= by
        by_contra H1
        simp at H1
        replace H1 : k + 1 ≤ 9:= by omega
        -- For any non-zero element in range(k+1), it's also in range(9)
        have g1 : ∀ x ∈ Finset.range (k + 1), x ≠ 0 → x ∈ Finset.range 9:= by
          intro x hx _
          simp at hx
          simp
          linarith
        -- The sum of elements in range(k+1) is less than or equal to the sum of elements in range(9)
        replace H1 : ∑ i in Finset.range (k + 1), i ≤ ∑ i in Finset.range 9, i:= by refine Finset.sum_le_sum_of_ne_zero g1
        rw [←H] at H1
        norm_num at H1
      -- If 40 = 1+2+...+k, then k must be less than 9
      have hk2 : k < 9:= by
        by_contra H2
        simp at H2
        -- For any non-zero element in range(10), it's also in range(k+1)
        have g1 : ∀ x ∈ Finset.range 10, x ≠ 0 → x ∈ Finset.range (k + 1):= by
          intro x hx _
          simp at hx
          simp
          linarith
        -- The sum of elements in range(10) is less than or equal to the sum of elements in range(k+1)
        replace H1 : ∑ i in Finset.range 10, i ≤ ∑ i in Finset.range (k + 1), i:= by refine Finset.sum_le_sum_of_ne_zero g1
        rw [←H] at H1
        norm_num at H1
      -- Contradiction: k cannot be both > 8 and < 9
      linarith
    .
      -- Prove that 40 cannot be written as p^k for any prime p and integer k
      intro k p hp
      by_contra H
      -- If 40 = p^k, then 2 and 5 must divide p^k
      have h1 : 2 ∣ p ^ k:= by rw [←H] ; omega
      have h2 : 5 ∣ p ^ k:= by rw [←H] ; omega
      -- If 2 divides p^k, then 2 divides p
      replace h1 : 2 ∣ p:= by exact Nat.Prime.dvd_of_dvd_pow g1 h1
      -- If 5 divides p^k, then 5 divides p
      replace h2 : 5 ∣ p:= by exact Nat.Prime.dvd_of_dvd_pow g2 h2
      -- If 2 divides p and p is prime, then p = 2
      replace h1 : 2 = 1 ∨ 2 = p:= by exact (Nat.dvd_prime hp).mp h1
      -- If 5 divides p and p is prime, then p = 5
      replace h2 : 5 = 1 ∨ 5 = p:= by exact (Nat.dvd_prime hp).mp h2
      simp at h1 h2
      -- Contradiction: p cannot be both 2 and 5
      linarith
    .
      -- Prove that 40 cannot be written as p+1 for any prime p
      intro p hp
      by_contra H
      -- If 40 = p+1, then p = 39
      replace H : p = 39:= by omega
      subst p
      -- Contradiction: 39 is not prime
      trivial
    .
      -- Prove that 40 cannot be written as p*q for distinct primes p and q
      intro p q hp hq hpq
      by_contra H
      -- If 40 = p*q, then 2 must divide p*q
      have h1 : 2 ∣ p * q:= by rw [←H] ; omega
      -- If 2 divides p*q, then 2 divides p or 2 divides q
      replace h1 : 2 ∣ p ∨ 2 ∣ q:= by exact (Nat.Prime.dvd_mul g1).mp h1
      rcases h1 with h1 | h1
      .
        -- If 2 divides p and p is prime, then p = 2
        replace h1 : 2 = 1 ∨ 2 = p:= by exact (Nat.dvd_prime hp).mp h1
        simp at h1
        rw [←h1] at H
        -- If 40 = 2*q, then q = 20
        replace H : q = 20:= by omega
        subst q
        -- Contradiction: 20 is not prime
        trivial
      .
        -- If 2 divides q and q is prime, then q = 2
        replace h1 : 2 = 1 ∨ 2 = q:= by exact (Nat.dvd_prime hq).mp h1
        simp at h1
        rw [←h1] at H
        -- If 40 = p*2, then p = 20
        replace H : p = 20:= by omega
        subst p
        -- Contradiction: 20 is not prime
        trivial
  .
    -- Prove that 40 is the smallest such number by checking all smaller positive integers
    simp [lowerBounds]
    intro n hn h1 h2 h3 h4
    -- Check that numbers 1 through 39 can all be expressed in at least one of the forms
    -- For each number, we apply the appropriate hypothesis to show it doesn't satisfy our conditions
    have g1:= h2 0 2 (by norm_num)
    have g2:= h2 1 2 (by norm_num)
    have g3:= h2 1 3 (by norm_num)
    have g4:= h2 2 2 (by norm_num)
    have g5:= h2 1 5 (by norm_num)
    have g6:= h4 2 3 (by norm_num) (by norm_num) (by omega)
    have g7:= h2 1 7 (by norm_num)
    have g8:= h2 3 2 (by norm_num)
    have g9:= h2 2 3 (by norm_num)
    have g10:= h4 2 5 (by norm_num) (by norm_num) (by omega)
    have g11:= h2 1 11 (by norm_num)
    have g12:= h3 11 (by norm_num)
    have g13:= h2 1 13 (by norm_num)
    have g14:= h4 2 7 (by norm_num) (by norm_num) (by omega)
    have g15:= h4 3 5 (by norm_num) (by norm_num) (by omega)
    have g16:= h2 4 2 (by norm_num)
    have g17:= h2 1 17 (by norm_num)
    have g18:= h3 17 (by norm_num)
    have g19:= h2 1 19 (by norm_num)
    have g20:= h3 19 (by norm_num)
    have g21:= h4 3 7 (by norm_num) (by norm_num) (by omega)
    have g22:= h4 2 11 (by norm_num) (by norm_num) (by omega)
    have g23:= h2 1 23 (by norm_num)
    have g24:= h3 23 (by norm_num)
    have g25:= h2 2 5 (by norm_num)
    have g26:= h4 2 13 (by norm_num) (by norm_num) (by omega)
    have g27:= h2 3 3 (by norm_num)
    have g28:= h1 7 (by omega)
    have g29:= h2 1 29 (by norm_num)
    have g30:= h3 29 (by norm_num)
    have g31:= h2 1 31 (by norm_num)
    have g32:= h3 31 (by norm_num)
    have g33:= h4 3 11 (by norm_num) (by norm_num) (by omega)
    have g34:= h4 2 17 (by norm_num) (by norm_num) (by omega)
    have g35:= h4 5 7 (by norm_num) (by norm_num) (by omega)
    have g36:= h1 8 (by omega)
    have g37:= h2 1 37 (by norm_num)
    have g38:= h4 2 19 (by norm_num) (by norm_num) (by omega)
    have g39:= h4 3 13 (by norm_num) (by norm_num) (by omega)
    -- Simplify all the hypotheses
    simp at g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39
    norm_num at g28 g36
    -- Complete the proof using the omega tactic
    omega
