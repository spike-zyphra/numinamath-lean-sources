import Mathlib

/- Exercise 10. Find all triplets ( $\mathbf{p , q , r} \mathbf{)}$ ) of prime numbers such that the 3 differences
$$ |p-q|,|q-r|,|r-p| $$
are also prime numbers. -/

theorem number_theory_293634 (p q r : ℕ) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hqr : (q - r).Prime) (hpr : (p - r).Prime) (hpq : (p - q).Prime) :
    (r, q, p) = (2, 5, 7) := by

  -- First we notice that, by the condition of primality, we must have p > q.
  have hpq' : p > q := by
    by_contra!
    simp only [this, Nat.sub_eq_zero_of_le] at hpq
    contradiction
  -- For the same reason, we must have q > r.
  have hqr' : q > r := by
    by_contra!
    simp only [this, Nat.sub_eq_zero_of_le] at hqr
    contradiction
  -- This implies that p is odd.
  have hp' : Odd p := by
    apply Nat.Prime.eq_two_or_odd' at hp
    rcases hp with h | h
    · rw [h] at hpq'
      apply Nat.Prime.two_le at hq
      linarith
    · exact h
  -- For the same reason, q is odd.
  have hq' : Odd q := by
    apply Nat.Prime.eq_two_or_odd' at hq
    rcases hq with h | h
    · rw [h] at hqr'
      apply Nat.Prime.two_le at hr
      linarith
    · exact h
  -- It follows that p - q is even, so it must be 2.
  have hpq'' : p = q + 2 := by
    apply Nat.Prime.eq_two_or_odd' at hpq
    rcases hpq with h | h
    · rw [add_comm, ← Nat.sub_eq_iff_eq_add (by linarith)]
      exact h
    · have := Nat.Odd.sub_odd hp' hq'
      rw [← Nat.not_even_iff_odd] at h
      contradiction
  -- Since p - r is prime and greater than 2, it must be odd. So r must be even, and since r is prime, it must be 2.
  have hr' : r = 2 := by
    apply Nat.Prime.eq_two_or_odd' at hr
    rcases hr with h | h
    · exact h
    · have : Even r := by
        have := Nat.Odd.sub_odd hp' h
        apply Nat.Prime.eq_two_or_odd' at hpr
        rcases hpr with h | h
        · omega
        · rw [← Nat.not_even_iff_odd] at h
          contradiction
      rw [← Nat.not_even_iff_odd] at h
      contradiction

  -- We recall that, from a previous result, if p, q, r are primes in arithmetic progression of ratio 2, then they must be 3, 5, and 7.
  have (p q r : ℕ) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
  (hpq : q = p + 2) (hqr : r = q + 2) :
  (p, q, r) = (3, 5, 7) := by
    mod_cases h : p % 3
    · -- If p is divisible by 3, then it must be equal to 3.
      rw [Nat.modEq_zero_iff_dvd, Nat.dvd_prime hp] at h
      simp only [OfNat.ofNat_ne_one, false_or] at h
      -- Substituting p = 3 into the equations for q and r, we get q = 5 and r = 7.
      rw [hqr, hpq, h.symm]
    · -- If p ≡ 1 (mod 3), then q must be divisible by 3, so q = 3.
      have : 3 ∣ q := by apply Nat.dvd_of_mod_eq_zero; rw [hpq, Nat.add_mod]; rw_mod_cast [h]
      simp only [Nat.dvd_prime hq, OfNat.ofNat_ne_one, false_or] at this
      simp only [← this, Nat.reduceEqDiff] at hpq
      -- But then p = 1, which is not prime.
      rw [hpq] at hp
      contradiction
    · -- If p ≡ 2 (mod 3), then r must be divisible by 3, so r = 3.
      have : 3 ∣ r := by apply Nat.dvd_of_mod_eq_zero; rw [hqr, hpq, add_assoc, Nat.add_mod]; rw_mod_cast [h]; norm_num
      simp only [Nat.dvd_prime hr, OfNat.ofNat_ne_one, false_or] at this
      simp only [← this, Nat.reduceEqDiff] at hqr
      -- But then q = 1, which is not prime.
      rw [hqr] at hq
      contradiction
  -- We use this fact on the triplet (q-r, q, p) to get the result.
  have := this (q-r) q p hqr hq hp (by rw [hr']; omega) hpq''
  simp only [Prod.mk.injEq] at this
  rw [hpq'', (by omega : q = q - r + r), this.1, hr']