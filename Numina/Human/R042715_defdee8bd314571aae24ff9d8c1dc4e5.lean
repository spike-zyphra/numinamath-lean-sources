import Mathlib

/- Let's determine those prime numbers $p$ and $q$ for which $p+q$ and $p^{2}+q^{2}-q$ are both prime numbers. -/
theorem number_theory_203434 (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (h1 : Nat.Prime (p + q)) (h2 : Nat.Prime (p ^ 2 + q ^ 2 - q)) :
    p = 3 ∧ q = 2 := by
  -- first prove bounds for p, q these will be useful
  have : 1 < q := by exact Nat.Prime.one_lt hq
  have : 1 < p := by exact Nat.Prime.one_lt hp
  -- prove p is odd
  have h_even_p : Odd p := by
    -- write p^2 + q^2 - q as p^2 + (q-1)*q = p^2 + (q-1)*(q-1+1), since (q-1)*(q-1+1) is even, p being even eimplies p^2 + q^2 - q is even
    have : p^2 + (q - 1) * q = p^2 + q^2 - q := by
      rw [Nat.sub_mul]
      ring_nf
      rw [Nat.add_sub_assoc]
      exact Nat.le_self_pow (by norm_num) q
    rw [← this] at h2
    by_contra h
    simp only [Nat.not_odd_iff_even] at h
    have : Even (p^2 + (q-1) * q) := by
      apply Even.add
      . exact (Nat.even_pow' (by norm_num)).mpr h
      . nth_rw 2 [show q = q-1 + 1 by omega]
        exact Nat.even_mul_succ_self _
    -- but even prime is 2, while 2^2 ≤ p^2, so p^2 + (q-1)*q can't be 2
    have h3 : p^2 + (q-1) * q = 2 := by exact (Nat.Prime.even_iff h2).mp this
    have h4 : 2^2 ≤ p^2 := Nat.pow_le_pow_of_le_left ‹1 < p› 2
    omega
  -- next we prove q = 2
  have hq' : q = 2 := by
    -- in particular we'll prove q is even (even prime is 2)
    rw [← Nat.Prime.even_iff hq]
    -- as p is odd, q being odd implies p + q even
    by_contra h
    simp at h
    have : Even (p + q) := by exact Odd.add_odd h_even_p h
    -- even prime is 2, but p + q is greater than 2 obviously, so q must be even
    rw [Nat.Prime.even_iff h1] at this
    linarith
  subst hq'
  -- prove an auxilariy lemma that modulo 3, x ≠ 0 implies x^2 + 2 = 0, by casework
  have aux (x : ZMod 3) (h : x ≠ 0) : x^2 + 2 = 0 := by
    fin_cases x <;> simp at h ⊢
    all_goals norm_cast
  -- p^2 + 2 after pluggin in q = 2, is larger than 3
  rw [show p^2 + 2^2 - 2 = p^2 + 2 by omega] at h2
  have : 1 + 2 < p^2 + 2 := by
    gcongr
    simp [‹1 < p›]
  -- by last fact and 3 ∣ p^2 + 2 implies 3 = p^2 + 2, we get p^2 + 2 ≠ 3
  have : ¬ 3 ∣ p^2 + 2 := by
    by_contra h
    linarith [(Nat.prime_dvd_prime_iff_eq (by norm_num) h2).mp h]
  -- we'll now prove p = 3
  have hp' : p = 3 := by
    -- we'll prove 3 ∣ p that will prove p = 3
    rw [eq_comm]
    apply (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp
    -- if ¬ 3 ∣ p, then we can use aux to prove 3 ∣ p^2 + 2, which is proven to be false
    by_contra h
    rw [← ZMod.natCast_zmod_eq_zero_iff_dvd] at h
    have := aux (p : ZMod 3) h
    norm_cast at this
    rw [ZMod.natCast_zmod_eq_zero_iff_dvd] at this
    contradiction
  subst hp'
  -- so we now have p = 3 and q = 2
  simp