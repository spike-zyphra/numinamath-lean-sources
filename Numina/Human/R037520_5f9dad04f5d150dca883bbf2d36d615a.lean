import Mathlib

open Nat

def is_prime (n : ℕ) := Nat.Prime n

def sum_of_two_primes (n : ℕ) :=
  ∃ p q, p.Prime ∧ q.Prime ∧ p + q = n

def diff_of_two_primes (n : ℕ) :=
  ∃ p q, p.Prime ∧ q.Prime ∧ p - q = n

theorem  number_theory_149956 : {n | is_prime n ∧ sum_of_two_primes n ∧diff_of_two_primes n} = {5} := by 
  ext n
  constructor

  --From left to right: the only such number is 5.
  intro h
  simp at h ⊢
  rcases h with ⟨h1, h2, h3⟩
  simp [is_prime] at h1
  simp [sum_of_two_primes] at h2
  simp [diff_of_two_primes] at h3

  obtain ⟨p1, p1p, q1, q1p, ha⟩ := h2
  obtain ⟨p2, p2p, q2, q2p, hm⟩ := h3

  --Wlog we assume that q1 ≤ p1.
  wlog p1leq1: q1 ≤ p1
  have q1lep1 : p1 ≤ q1 := by linarith
  apply this
  exact h1
  exact q1p
  exact p1p
  linarith
  exact p2p
  exact q2p
  linarith
  linarith

  have : 2 ≤ n := by exact Prime.two_le h1
  have q2lep2 : q2 ≤ p2 := by omega

  have p1ge2 : 2 ≤ p1 := by exact Prime.two_le p1p
  have q1ge2 : 2 ≤ q1 := by exact Prime.two_le q1p
  have p2ge2 : 2 ≤ p2 := by exact Prime.two_le p2p
  have q2ge2 : 2 ≤ q2 := by exact Prime.two_le q2p

  --n cannot be 2, since otherwise it cannot be the sum of two primes.
  have nne2: n ≠ 2 := by 
    by_contra ne2
    rw [ne2] at ha
    linarith
  --So n has to be odd.
  have : Odd n := by exact Prime.odd_of_ne_two h1 nne2

  --Then, p1 and q1 cannot both be odd, so q1 is 2.
  have q1eq: q1 = 2 := by 
    have : Even p1 ∨ Even q1 := by 
      by_contra h
      push_neg at h
      obtain ⟨neven1,neven2⟩ := h
      have oddp1: Odd p1 := by exact not_even_iff_odd.mp neven1
      have oddq1: Odd q1 := by exact not_even_iff_odd.mp neven2
      have : Even (p1+q1) := by exact Odd.add_odd oddp1 oddq1
      rw [ha] at this
      have : n = 2 := by exact (Prime.even_iff h1).mp this
      contradiction
    rcases this with evenp1 | evenq1
    have : p1 = 2 := by exact (Prime.even_iff p1p).mp evenp1
    have : q1 = 2 := by linarith
    have : n = 4 := by linarith
    rw [this] at h1
    norm_num at h1
    exact (Prime.even_iff q1p).mp evenq1
  --Similarly, for p2 and q2, they cannot both be odd, so q2 is 2.
  have q2eq: q2 = 2 := by 
    have : Even p2 ∨ Even q2 := by
      by_contra h
      push_neg at h
      obtain ⟨neven1,neven2⟩ := h
      have oddp2: Odd p2 := by exact not_even_iff_odd.mp neven1
      have oddq2: Odd q2 := by exact not_even_iff_odd.mp neven2
      have : Even (p2 - q2) := by exact Nat.Odd.sub_odd oddp2 oddq2
      rw [hm] at this
      have : n =2 := by exact (Prime.even_iff h1).mp this
      contradiction
    rcases this with evenp2 | evenq2
    have p2eq: p2 = 2 := by exact (Prime.even_iff p2p).mp evenp2
    have q2eq: q2 = 2 := by linarith
    have : n = 0 := by rw [←hm]; rw [p2eq,q2eq]; 
    rw [this] at h1
    norm_num at h1
    exact (Prime.even_iff q2p).mp evenq2

  --Then, we chech p1 % 3. It can only happen that p1 % 3 = 0.
  --So we get that p1 = 3 and then n = 5.
  have p1eq: p1 = 3 := by 
    have : 3 ∣ p1 := by 
      have : p1 % 3 = 0 ∨ p1 % 3 = 1 ∨ p1 % 3 = 2 := by omega
      rcases this with mod0 | mod1 | mod2
      exact dvd_of_mod_eq_zero mod0
      exfalso
      have : (p1 +2) % 3 = 0 := by omega
      have : n % 3 = 0 := by omega
      have : 3 ∣ n := by exact dvd_of_mod_eq_zero this
      have : n = 3 := by 
        rw [Nat.Prime.dvd_iff_eq] at this
        exact this
        exact h1
        norm_num
      linarith
      exfalso
      have : (p1 + 4) % 3 = 0 := by omega
      have : p2 % 3 = 0 := by omega
      have : 3 ∣ p2 := by exact dvd_of_mod_eq_zero this
      have p2e: p2 = 3 := by 
        rw [Nat.Prime.dvd_iff_eq] at this
        exact this
        exact p2p
        norm_num
      have ne1: n = 1 := by omega
      rw [ne1] at h1
      norm_num at h1

    rw [Nat.Prime.dvd_iff_eq] at this
    exact this
    exact p1p
    norm_num

  rw [p1eq,q1eq] at ha
  rw [← ha]
  norm_num


  --For the other direction. A simple verification.
  intro h
  simp [is_prime, sum_of_two_primes, diff_of_two_primes]
  constructor
  rw [h]
  norm_num
  constructor
  use 2
  norm_num
  use 3
  rw [h]
  norm_num

  use 7
  norm_num
  use 2
  rw [h]
  norm_num
  