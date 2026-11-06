import Mathlib

/- (Ireland 1996) Let $p$ be a prime number and $a, n$ be strictly positive integers. Prove that if $2^{p}+3^{p}=a^{n}$, then necessarily $n=1$. -/

theorem number_theory_124518 (p : ℕ) (hp : Nat.Prime p) (a n : ℕ) (hn : 0 < n)
    (h : 2^p + 3^p = a^n) : n = 1 := by

  -- If p is prime, then p is odd or p = 2.
  rcases Nat.Prime.eq_two_or_odd' hp with (h2 | hodd)
  · -- If p = 2, then 2^2 + 3^2 = 13 which is not a perfect power.
    rw [h2] at h
    norm_num at h
    exact ((Nat.Prime.pow_eq_iff (by decide)).mp h.symm).2
  · -- If p is odd, then 2^p + 3^p is a multiple of 5. Since 5 is prime, so is a.
    have h5 : 5 ∣ a := by
      obtain ⟨k, hk⟩ := hodd
      rw [hk] at h
      -- We show that 2^p + 3^p is congruent to 0 mod 5.
      have zmod5 : a ^ n = (0 : ZMod 5) := by
        rw_mod_cast [← h]
        have : (-1 : ZMod 5) ^ (2 * k + 1) = -1 := by rw [pow_add, pow_mul, pow_one]; norm_num
        simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
        rw [add_eq_zero_iff_eq_neg, (by rfl : (3 : ZMod 5) = -2), neg_eq_neg_one_mul, ← this, ← mul_pow]
        ring
      norm_cast at zmod5
      exact Nat.Prime.dvd_of_dvd_pow (by decide) ((ZMod.natCast_zmod_eq_zero_iff_dvd (a^n) 5).mp zmod5)
    -- Since 5 ∣ a, if n > 1 then 25 ∣ a^n. We want to show that this happens only if p is 5.
    have h25 : 25 ∣ 2 ^ p + 3 ^ p → 5 ∣ p := by
      intro hp'
      have h25 : (2 ^ p + 3 ^ p : ℕ) = (0 : ZMod 25) := by rw [ZMod.natCast_zmod_eq_zero_iff_dvd]; exact hp'
      simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] at h25
      rw [← eq_neg_iff_add_eq_zero] at h25
      -- This is the core of the proof. We show that 2^p + 3^p is not congruent to 0 mod 25.
      suffices (2 : ZMod 25) ^ p * (17 : ZMod 25) ^ p = -1 by
        rw [← mul_pow, (by rfl : 2 * 17 = (9 : ZMod 25))] at this
        -- We have that 9^p = -1 mod 25. This means that the order of 9 mod 25 divides 2 * p.
        have : 9 ^ (2 * p) = (1 : ZMod 25) := by rw [mul_comm, pow_mul, this]; norm_num
        -- But the order of 9 mod 25 is 10, so 10 must divide 2 * p.
        have ord9 : orderOf (9 : ZMod 25) = 10 := by
          rw [orderOf_eq_iff (by linarith)]
          constructor
          · norm_num; rfl
          · intro m hm hm'
            interval_cases m <;> decide
        -- So if 25 ∣ 2^p + 3^p, then 10 ∣ 2 * p. This means that p must be 5.
        have : 10 ∣ 2 * p := by rw [← ord9]; exact orderOf_dvd_of_pow_eq_one this
        rcases (Nat.Prime.dvd_mul (by decide : Nat.Prime 5)).mp (dvd_trans (by norm_num : 5 ∣ 10) this)
        · contradiction
        · assumption
      rw [h25, neg_mul, ← mul_pow, (by rfl : 3 * 17 = (1 : ZMod 25))]
      simp
    -- Now we treat the cases p = 5 and p ≠ 5 separately.
    by_cases h' : 5 ∣ p
    · -- If p = 5, then 2^5 + 3^5 = 275 which is not a perfect power.
      have p5 : p = 5 := by
        have := (Nat.dvd_prime hp).mp h'
        simp only [OfNat.ofNat_ne_one, false_or] at this
        exact this.symm
      rw [p5] at h
      norm_num at h
      have h11 : 11 ∣ 275 := by norm_num
      rw [h] at h11
      apply Nat.Prime.dvd_of_dvd_pow (by decide) at h11
      by_contra hn'
      have : 2 ≤ n := by by_contra!; interval_cases n; contradiction
      have := dvd_trans (pow_dvd_pow_of_dvd h11 2) (Nat.pow_dvd_pow a this)
      rw [← h] at this
      contradiction
    · -- If p ≠ 5, then ¬ 25 ∣ 2^p + 3^p. This leads to a contradiction because 5 | 2^p + 3^p.
      have h' := fun a ↦ h' (h25 a)
      rw [h] at h'
      by_contra hn'
      apply h'
      have : 2 ≤ n := by by_contra!; interval_cases n; contradiction
      exact dvd_trans (pow_dvd_pow_of_dvd h5 2) (Nat.pow_dvd_pow a this)