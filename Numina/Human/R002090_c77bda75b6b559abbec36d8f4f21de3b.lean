import Mathlib

/- A pair of numbers are [i]twin primes[/i] if they differ by two, and both are prime. Prove that, except for the pair $\{3, 5\}$, the sum of any pair of twin primes is a multiple of $ 12$. -/
theorem number_theory_63629 (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (h : q = p + 2) :
  (p ≠ 3 ∨ q ≠ 5) → 12 ∣ p + q := by

  have : 2 ≤ p := by exact Nat.Prime.two_le hp
  have : 4 ≤ q := by linarith

  --We will prove that 3 ∣ p+q and 4 ∣ p+q. Since (3,4) = 1, we are done.
  intro pe3qn5

  --We have 3 ∣ p+q, by enumerating p's residues modulo 3.
  have d3: 3 ∣ p+q := by 
    have p3: Nat.Prime 3 := by norm_num
    
    by_cases m0 : p % 3 = 0
    have pd3: 3 ∣ p := by exact Nat.dvd_of_mod_eq_zero m0
    have : p = 3 := by exact Eq.symm ((fun {p q} pp qp => (Nat.prime_dvd_prime_iff_eq pp qp).mp) p3 hp pd3)
    rw [this] at h; norm_num at h
    tauto

    by_cases m1 : p % 3 = 1
    have : (p+2) % 3 = 0 := by omega
    rw [←h] at this
    have q3: 3 ∣ q := by exact Nat.dvd_of_mod_eq_zero this
    have : q = 3 := by exact Eq.symm ((fun {p q} pp qp => (Nat.prime_dvd_prime_iff_eq pp qp).mp) p3 hq q3)
    linarith

    have m2 : p % 3 = 2 := by omega
    have : (p+2) % 3 = 1 := by omega
    rw [←h] at this
    have : (p+q) % 3 = 0 := by omega
    exact Nat.dvd_of_mod_eq_zero this
    
  --We have 4 ∣ p+q, by enumerating p's residues modulo 4.
  have d4: 4 ∣ p+q := by
    by_cases m0 : p % 4 = 0
    have : 4 ∣ p := Nat.dvd_of_mod_eq_zero m0
    obtain ⟨k,hk⟩ := this
    have : Even p := by use 2*k; simp [hk]; ring
    have : p = 2 := by exact (Nat.Prime.even_iff hp).mp this
    have : q = 4 := by linarith
    rw [this] at hq; norm_num at hq

    by_cases m1 : p % 4 = 1
    have : q % 4 = 3 := by omega
    have : (p+q) % 4 = 0 := by omega
    exact Nat.dvd_of_mod_eq_zero this

    by_cases m2 : p % 4 = 2
    have : q % 4 = 0 := by omega
    have : 4 ∣ q := by exact Nat.dvd_of_mod_eq_zero this
    obtain ⟨k,hk⟩ := this
    have : Even q := by use 2 * k; simp [hk]; ring
    have : q = 2 := by exact (Nat.Prime.even_iff hq).mp this
    linarith

    have m3 : p % 4 = 3 := by omega
    have : q % 4 = 1 := by omega
    have : (p+q) % 4 = 0 := by omega
    exact Nat.dvd_of_mod_eq_zero this




  have c34: Nat.Coprime 3 4 := by norm_num
  have : 12 = 3 * 4 := by norm_num
  rw [this]
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd c34 d3 d4
