import Mathlib

lemma dirichlet's_theorem (a b: ℕ) (h: Nat.Coprime a b) :
    ∀ n, ∃ p, Nat.Prime p ∧ p % b = a % b ∧ n < p := by
      sorry

/- Let $n$ be a positive integer. Determine, in terms of $n$,
the greatest integer which divides every number of the form $p+1$,
where $p \equiv 2 \bmod 3$ is a prime number which does not divide $n$.
## Proposed by Bulgaria -/

theorem number_theory_604279 (n : ℕ) (hn : n > 0) :
    IsGreatest {k | ∀ p, (Nat.Prime p ∧ p % 3 = 2 ∧ ¬p ∣ n) → k ∣ (p + 1)} (if Odd n then 3 else 6) := by

    constructor

    -- the forward direction
    .
      simp
      intro p h1 h2 h3
      by_cases o: Odd n
      .
        simp [o]
        apply Nat.dvd_of_mod_eq_zero
        rw [Nat.add_mod]
        simp [h2]
      .
        simp [o]
        have s: p ≠ 2 := by
          by_contra! s
          simp at o
          simp [s] at h3
          absurd h3
          simp
          apply Nat.mod_eq_zero_of_dvd
          apply Even.two_dvd o
        have v: Odd p := by
          apply Nat.Prime.odd_of_ne_two h1 s
        have d1: 3 ∣ p + 1 := by
          apply Nat.dvd_of_mod_eq_zero
          rw [Nat.add_mod]
          simp [h2]
        have d2: 2 ∣ p + 1 := by
          apply Nat.dvd_of_mod_eq_zero
          rw [Nat.add_mod]
          replace v: p % 2 = 1 := by
            by_contra! t
            simp at t
            apply Nat.dvd_of_mod_eq_zero at t
            rw [← even_iff_two_dvd] at t
            absurd v
            simp [t]
          simp [v]
        rw [show 6 = 2 * 3 by rfl]
        apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
        norm_num
        exact d2
        exact d1


    -- the backward direction
    .
      intro k h
      simp at h
      by_cases o: Odd n

      -- case Odd n
      .
        simp [o]
        specialize h 2
        norm_num at h
        have u: n % 2 = 1 := by
          by_contra! t
          simp at t
          apply Nat.dvd_of_mod_eq_zero at t
          absurd o
          rw [← even_iff_two_dvd] at t
          simp [t]
        simp [u] at h
        apply Nat.le_of_dvd at h
        exact h
        norm_num

      -- case Even n
      .
        simp [o]
        simp at o

        -- it suffices to show the following three arguments using dirichlet's theorem
        have h1: ∃ p, Nat.Prime p ∧ p % 3 = 2 ∧ ¬p ∣ n ∧ ¬ 4 ∣ p + 1 := by
          have j:= dirichlet's_theorem 5 12
          norm_num at j
          specialize j n
          obtain ⟨p, h1, h2, h3⟩ := j
          use p
          simp [h1]
          constructor
          .
            rw [show p % 3 = p % 12 % 3 by symm; rw [Nat.mod_mod_of_dvd]; omega]
            rw [h2]
          .
            constructor
            .
              by_contra! t
              apply Nat.le_of_dvd at t
              omega
              linarith
            .
              by_contra! t
              apply Nat.mod_eq_zero_of_dvd at t
              rw [Nat.add_mod] at t
              rw [show p % 4 = p % 12 % 4 by symm; rw [Nat.mod_mod_of_dvd]; omega] at t
              simp [h2] at t

        have h2: ∃ p, Nat.Prime p ∧ p % 3 = 2 ∧ ¬p ∣ n ∧ ¬ 9 ∣ p + 1 := by
          have j:= dirichlet's_theorem 2 9
          norm_num at j
          specialize j n
          obtain ⟨p, h1, h2, h3⟩ := j
          use p
          simp [h1]
          constructor
          .
            rw [show p % 3 = p % 9 % 3 by symm; rw [Nat.mod_mod_of_dvd]; omega]
            rw [h2]
          .
            constructor
            .
              by_contra! t
              apply Nat.le_of_dvd at t
              omega
              linarith
            .
              by_contra! t
              apply Nat.mod_eq_zero_of_dvd at t
              rw [Nat.add_mod] at t
              rw [show p % 9 = p % 9 % 9 by symm; rw [Nat.mod_mod_of_dvd]; omega] at t
              simp [h2] at t

        have h3: ∀ q, Nat.Prime q → q ≠ 2 → q ≠ 3 → ∃ p, Nat.Prime p ∧ p % 3 = 2 ∧ ¬p ∣ n ∧ ¬ q ∣ p + 1 := by
          intro q hq n1 n2
          have j:= dirichlet's_theorem 2 (3 * q)
          have o: Nat.Coprime 2 (3 * q) := by
            apply Nat.Coprime.mul_right
            .
              norm_num
            .
              rw [Nat.Prime.coprime_iff_not_dvd]
              by_contra! t
              replace t: Even q := by
                rw [even_iff_two_dvd]
                exact t
              absurd t
              simp
              apply Nat.Prime.odd_of_ne_two
              exact hq
              exact n1
              norm_num
          simp [o] at j
          have o2: Odd q := by
            apply Nat.Prime.odd_of_ne_two
            exact hq
            exact n1
          have o3: Odd (3 * q) := by
            apply Odd.mul
            decide
            exact o2
          simp [o3] at j
          clear o o2 o3
          specialize j n
          obtain ⟨p, h1, h2, h3⟩ := j
          use p
          simp [h1]
          constructor
          .
            rw [show p % 3 = p % (3 * q) % 3 by symm; rw [Nat.mod_mod_of_dvd]; omega]
            rw [h2]
            rw [Nat.mod_mod_of_dvd]
            simp
          .
            constructor
            .
              by_contra! t
              apply Nat.le_of_dvd at t
              omega
              linarith
            .
              by_contra! t
              apply Nat.mod_eq_zero_of_dvd at t
              rw [Nat.add_mod] at t
              rw [show p % q = p % (3 * q) % q by symm; rw [Nat.mod_mod_of_dvd]; simp] at t
              rw [h2] at t
              norm_num at t
              apply Nat.dvd_of_mod_eq_zero at t
              apply Nat.le_of_dvd at t
              interval_cases q
              .
                norm_num at hq
              .
                norm_num at hq
              .
                trivial
              .
                trivial
              norm_num

        -- use h3, we know that there are no prime factor other than 2 and 3 that divides k
        replace h3: ∀ q, Nat.Prime q → q ≠ 2 → q ≠ 3 → ¬ q ∣ k := by
          by_contra! t
          obtain ⟨q, hq, n1, n2, s⟩ := t
          specialize h3 q hq n1 n2
          obtain ⟨p, hp1, hp2, hp3, hp4⟩ := h3
          specialize h p hp1 hp2 hp3
          absurd hp4
          apply dvd_trans s h

        -- use h2, we see that 9 does not divide k
        replace h2: ¬ 9 ∣ k := by
          by_contra! t
          obtain ⟨p, hp1, hp2, hp3, hp4⟩ := h2
          absurd hp4
          specialize h p hp1 hp2 hp3
          apply dvd_trans t h

        -- use h1, we see that 4 does not divide k
        replace h1: ¬ 4 ∣ k := by
          by_contra! t
          obtain ⟨p, hp1, hp2, hp3, hp4⟩ := h1
          absurd hp4
          specialize h p hp1 hp2 hp3
          apply dvd_trans t h

        clear h o hn
        let s:= Nat.primeFactors k
        have hs: s ⊆ {2, 3} := by
          intro x hx
          simp [s] at hx
          simp
          by_contra! l
          rcases l with ⟨l1, l2⟩
          rcases hx with ⟨p1, p2, p3⟩
          specialize h3 x p1 l1 l2
          trivial
        have hi: k ≠ 0 := by
          by_contra! o
          simp [o] at h2
        have i:= Nat.factorization_prod_pow_eq_self hi
        rw [Nat.prod_factorization_eq_prod_primeFactors] at i
        have j:  ∏ p ∈ k.primeFactors, p ^ k.factorization p ≤
           ∏ p ∈ {2, 3}, p ^ k.factorization p := by
            apply Finset.prod_le_prod_of_subset_of_one_le'
            simp [s] at hs
            exact hs
            intro i u v
            apply Nat.one_le_pow
            simp at u
            omega
        rw [i] at j
        clear i
        rw [Finset.prod_insert] at j
        rw [Finset.prod_singleton] at j

        -- then we show the pow of 2 and 3 are at most 1
        have s1: k.factorization 2 ≤ 1 := by
          by_contra! t
          replace t: 2 ≤ k.factorization 2 := by
            omega
          rw [← Nat.Prime.pow_dvd_iff_le_factorization] at t
          simp at t
          trivial
          norm_num
          omega
        have s2: k.factorization 3 ≤ 1 := by
          by_contra! t
          replace t: 2 ≤ k.factorization 3 := by
            omega
          rw [← Nat.Prime.pow_dvd_iff_le_factorization] at t
          simp at t
          trivial
          norm_num
          omega
        have r1: 2 ^ k.factorization 2 ≤ 2 ^ 1:= by
          apply Nat.pow_le_pow_of_le_right
          norm_num
          exact s1
        have r2: 3 ^ k.factorization 3 ≤ 3 ^ 1:= by
          apply Nat.pow_le_pow_of_le_right
          norm_num
          exact s2
        simp at r1 r2
        set x:= 2 ^ k.factorization 2
        set y:= 3 ^ k.factorization 3
        have ux: 1 ≤ x := by
          apply Nat.one_le_pow
          norm_num
        have uy: 1 ≤ y := by
          apply Nat.one_le_pow
          norm_num
        nlinarith
        decide