import Mathlib

-- we present the following lemma: any odd n, if n is not 1 and not prime, then either n = ab with a ≠ b, or n = p^2
lemma not_prime_not_nine_exist (n: ℕ) (h1: ¬ Nat.Prime n) (h2: Odd n) (h3: n ≠ 1):
  (∃ a b, 3 ≤ a ∧ a < b ∧ n = a * b) ∨ (∃ p, Nat.Prime p ∧ n = p ^ 2) := by

    -- we first take one odd prime factor p of n
    set s:= Nat.primeFactors n
    have hs: s ≠ ∅ := by
      by_contra! hs
      rw [Nat.primeFactors_eq_empty] at hs
      have p: n ≠ 0 := by
        by_contra! p
        simp [p] at h2
      omega
    replace hs: s.Nonempty := by
      by_contra! ls
      simp at ls
      trivial
    apply Finset.Nonempty.exists_mem at hs
    obtain ⟨p, hp⟩ := hs
    simp [s] at hp
    rcases hp with ⟨pp, hp, i⟩
    have lp: 3 ≤ p := by
      by_contra! o
      interval_cases p
      all_goals norm_num at pp
      absurd h2
      simp
      rw [even_iff_two_dvd]
      exact hp

    -- then we show the rest
    set q:= n / p
    have r: n = p * q := by
      simp [q]
      rw [Nat.mul_div_cancel_left']
      exact hp
    by_cases j: p = q
    .
      right
      use p
      simp [pp]
      simp [← j] at r
      simp [r]
      ring
    .
      by_cases l: p < q
      .
        left
        use p, q
      .
        left
        use q, p
        replace j: q < p := by omega
        simp [j]
        constructor
        .
          by_contra! s
          interval_cases q
          .
            simp at r
            simp [r] at h2
          .
            simp [r] at h1
            trivial
          .
            replace r: 2 ∣ n := by
              rw [r]
              simp
            absurd h2
            simp [even_iff_two_dvd, r]
        .
          rw [r]
          ring

-- we show that any distinct prod less than n divides n!
lemma factorial_mul_dvd (a b c d: ℕ) (h0: 0 < a) (h1: a < b) (h2: b < c) (h3: c < d):
  a * b * c * d ∣ Nat.factorial d := by
    nth_rewrite 2 [show d = d - 1 + 1 by omega]
    rw [Nat.factorial_succ]
    rw [show d - 1 + 1 = d by omega]
    rw [show a * b * c * d = d * (a * b * c) by ring]
    apply Nat.mul_dvd_mul_left
    have u: Nat.factorial c ∣ Nat.factorial (d - 1) := by
      apply Nat.factorial_dvd_factorial
      omega
    suffices a * b * c ∣ Nat.factorial c by apply dvd_trans this u
    clear u
    nth_rewrite 2 [show c = c - 1 + 1 by omega]
    rw [Nat.factorial_succ]
    rw [show c - 1 + 1 = c by omega]
    rw [show a * b * c = c * (a * b) by ring]
    apply Nat.mul_dvd_mul_left
    have u: Nat.factorial b ∣ Nat.factorial (c - 1) := by
      apply Nat.factorial_dvd_factorial
      omega
    suffices a * b ∣ Nat.factorial b by apply dvd_trans this u
    clear u
    nth_rewrite 2 [show b = b - 1 + 1 by omega]
    rw [Nat.factorial_succ]
    rw [show b - 1 + 1 = b by omega]
    rw [show a * b = b * a by ring]
    apply Nat.mul_dvd_mul_left
    have u: Nat.factorial a ∣ Nat.factorial (b - 1) := by
      apply Nat.factorial_dvd_factorial
      omega
    suffices a ∣ Nat.factorial a by apply dvd_trans this u
    clear u
    apply Nat.dvd_factorial
    omega
    simp


/-Find all odd natural numbers n such that
(n−1)! is not divisible by n^2 -/

theorem number_theory_125038: {n: ℕ | Odd n ∧ ¬ n ^ 2 ∣Nat.factorial (n - 1)} =
  {n: ℕ | Nat.Prime n ∧ Odd n} ∪ {9} := by

    ext n
    constructor

    -- the forward direction
    .
      intro h
      simp only [Set.mem_setOf_eq] at h
      rcases h with ⟨hn, h⟩
      simp
      by_contra! f
      rcases f with ⟨ne, f⟩
      absurd h
      replace f: ¬ Nat.Prime n := by
        by_contra! g
        simp [g] at f
        absurd f
        simp [hn]
      have c: n ≠ 1 := by
        by_contra! c
        simp [c] at h
      have g:= not_prime_not_nine_exist n f hn c
      clear f h
      rcases g with g | g

      -- case 1: n = ab, use a, 2a, b, 2b
      .
        obtain ⟨a, b, h1, h2, h3⟩ := g
        have o1: Nat.factorial (2 * b) ∣ Nat.factorial (n - 1) := by
          apply Nat.factorial_dvd_factorial
          simp [h3]
          have u: 1 < a * b := by nlinarith
          zify
          rw [show ↑(a * b - (1: ℕ)) = a * b - (1: ℤ) by apply Int.natCast_sub; omega]
          nlinarith
        suffices n ^ 2 ∣ Nat.factorial (2 * b) by apply dvd_trans this o1
        have o2: n ^ 2∣ a * (2 * a) * b * (2 * b) := by
          rw [h3]
          rw [show a * (2 * a) * b * (2 * b) = 4 * (a * b) ^ 2 by ring]
          simp
        suffices a * (2 * a) * b * (2 * b) ∣ Nat.factorial (2 * b) by apply dvd_trans o2 this

        -- then we use the lemma
        by_cases r: 2 * a < b
        .
          apply factorial_mul_dvd a (2 * a) b (2 * b)
          omega
          omega
          exact r
          omega
        .
          simp at r
          have o: b ≠ 2 * a := by
            by_contra! o
            simp [o] at h3
            have v: 2 ∣ n := by
              rw [h3]
              rw [show a * (2 * a) = 2 * a ^ 2 by ring]
              simp
            rw [← even_iff_two_dvd] at v
            absurd hn
            simp [v]
          rw [show a * (2 * a) * b * (2 * b) = a * b * (2 * a) * (2 * b) by ring]
          apply factorial_mul_dvd a b (2 * a) (2 * b) (by omega) (by omega) (by omega) (by omega)

      -- case 2: n = p^2
      .
        obtain ⟨p, hp, h⟩ := g
        have o: Nat.factorial (4 * p) ∣ Nat.factorial (n - 1) := by
          apply Nat.factorial_dvd_factorial
          simp [h]
          have lp: 5 ≤ p := by
            by_contra! l
            interval_cases p
            all_goals norm_num at hp
            .
              simp [h] at hn
              absurd hn
              decide
            .
              simp [h] at ne

          zify
          have o: ↑(p ^ 2 - (1: ℕ)) = p ^ 2 - (1: ℤ) := by
            apply Int.natCast_sub
            nlinarith
          rw [o]
          clear o
          nlinarith
        suffices n ^ 2 ∣ Nat.factorial (4 * p) by apply dvd_trans this o
        clear o
        have up: 0 < p := by
          by_contra! u
          replace u: p = 0 := by
            omega
          simp [u] at hp
          norm_num at hp
        have i:= factorial_mul_dvd p (2 * p) (3 * p) (4 * p) (by omega) (by omega) (by omega) (by omega)
        have j: n ^ 2 ∣ p * (2 * p) * (3 * p) * (4 * p) := by
          rw [show n ^ 2 = p ^ 4 by rw [h]; ring]
          rw [show p * (2 * p) * (3 * p) * (4 * p) = 24 * p ^ 4 by ring]
          simp
        apply dvd_trans j i



    -- the backward direction
    .
      intro h
      simp at h
      rcases h with h | h
      -- case 1: n = 9
      .
        simp [h]
        decide
      .
        rcases h with ⟨pn, hn⟩
        simp [hn]
        by_contra! f
        replace f: n ∣ Nat.factorial (n - 1) := by
          have g: n ∣ n ^ 2 := by
            rw [show n ^ 2 = n * n by ring]
            simp
          apply dvd_trans g f

        have s: n ∣ Nat.factorial (n - 1) ↔ n ≤ (n - 1) := by
          apply Nat.Prime.dvd_factorial pn
        rw [s] at f
        have o: 1 ≤ n := by
          by_contra! o
          replace o: n = 0 := by
            omega
          simp [o] at hn
        omega