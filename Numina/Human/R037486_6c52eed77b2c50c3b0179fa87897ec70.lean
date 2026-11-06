import Mathlib

open Nat ArithmeticFunction

/- Prove that for every integer $n$ greater than 1 ,

$$
\sigma(n) \phi(n) \leq n^{2}-1
$$

When does equality hold? -/

theorem numbera_theory_608225{n:ℕ}(hn: n > 1):
  σ 1 n * φ n ≤ n^2 - 1 := by
  -- consider prime factorization of n. n is either prime power,
  -- or product of two coprime numbers smaller than n.
  have n_cases{nn:ℕ}(hnn: nn > 1): (∃ m1 m2, m1*m2 = nn ∧
    m1.Coprime m2 ∧ m1 < nn ∧ m2 < nn ∧ 1 < m1 ∧ 1 < m2) ∨
    (∃ p k, Nat.Prime p ∧ nn = p^k) := by
    rcases (exists_prime_and_dvd hnn.ne') with ⟨p, hp⟩
    have nn_nz: nn ≠ 0 := ne_zero_of_lt hnn
    rcases (exists_eq_pow_mul_and_not_dvd nn_nz p
      hp.left.ne_one) with ⟨k, m, not_dvd, rfl⟩
    -- suppose n = p^k m and m coprime to p.
    -- then if m = 1, n is prime power.
    -- otherwise it is product of two coprime numbers < n.
    by_cases hm: m = 1
    · right
      use p,k
      simp [hp.left, hm]
    · left
      use (p^k),m
      have co: (p^k).Coprime m := by
        refine Coprime.pow_left k ?_
        exact (Nat.Prime.coprime_iff_not_dvd hp.left).mpr not_dvd
      refine ⟨rfl, co, ?_⟩
      have h1: 1 < m := by
        have: m ≠ 0 := Nat.ne_zero_of_mul_ne_zero_right nn_nz
        omega
      -- p ∣ n, or, p ∣ p^k m, and m is coprime to p.
      -- then p ∣ p^k, k cannot be zero.
      have knz: k ≠ 0 := by
        have: p ∣ p^k := by
          have := hp.right
          rw [Nat.Prime.dvd_mul hp.left] at this
          rcases this with hh | hh
          · exact hh
          · exfalso; apply not_dvd hh
        by_contra! kz
        simp only [kz, pow_zero, dvd_one] at this
        simp only [this, one_pow, one_mul, isUnit_one,
        IsUnit.dvd, and_true] at hp
        norm_num at hp
      -- thereby 1 < p^k
      have h2: 1 < p^k := by
        apply Nat.one_lt_pow knz hp.left.one_lt
      refine ⟨?_, ?_, h2, h1⟩
      · refine (Nat.lt_mul_iff_one_lt_right ?_).mpr h1
        exact zero_lt_of_lt h2
      · apply (Nat.lt_mul_iff_one_lt_left ?_).mpr h2
        exact zero_lt_of_lt h1
  -- back to the problem.
  -- use strong induction on n.
  induction' n using Nat.strong_induction_on with n ih
  rcases (n_cases hn) with h | h
  · -- if n is not prime power, then by multiplicity of σ and φ
    -- easy to reach the result.
    rcases h with ⟨m1, m2, n_of_m, co, hm1, hm2, hm1', hm2'⟩
    rw [← n_of_m]
    have npos: 0 < n := by exact zero_lt_of_lt hn
    rw [← n_of_m] at npos
    replace npos := npos.ne'
    have m1nz: m1 ≠ 0 := Nat.ne_zero_of_mul_ne_zero_left npos
    have m2nz: m2 ≠ 0 := Nat.ne_zero_of_mul_ne_zero_right npos
    -- σ is multiplicative and m1m2 coprime, so σ (m1 m2) = σ m1 σ m2
    have h1: σ 1 (m1 * m2) = σ 1 m1 * σ 1 m2 := by
      have: IsMultiplicative (σ 1) := isMultiplicative_sigma
      rw [IsMultiplicative.iff_ne_zero] at this
      exact this.right m1nz m2nz co
    -- same for φ m1 m2
    have h2: φ (m1 * m2) = φ m1 * φ m2 := totient_mul co
    --therefore by induction, σ (m) φ (m) ≤ m^2 - 1
    have h3: σ 1 (m1 * m2) * φ (m1 * m2) ≤
      (m1^2 - 1) * (m2^2 - 1) := by
      rw [h1, h2]
      rw [← one_le_iff_ne_zero] at m1nz m2nz
      rw [← mul_assoc, mul_assoc (σ 1 m1), mul_comm (σ 1 m2),
      ← mul_assoc, mul_assoc _ _ (φ m2)]
      apply Nat.mul_le_mul ?_ ?_
      · apply ih m1 hm1 hm1'
      · apply ih m2 hm2 hm2'
    -- easy to see (m1^2-1)(m2^2-1) ≤ (m1m2)^2-1
    have h4: (m1^2-1)*(m2^2-1) ≤ (m1*m2)^2 - 1 := by
      have hh1: 1 < m1^2 := by
        apply Nat.one_lt_pow (by norm_num) hm1'
      have hh2: 1 < m2^2 := by
        apply Nat.one_lt_pow (by norm_num) hm2'
      have hh3: 1 ≤ (m1*m2)^2 := by
        apply one_le_pow
        rw [n_of_m]
        exact zero_lt_of_lt hn
      zify
      rw [Nat.cast_sub (le_of_lt hh1), Nat.cast_sub (le_of_lt hh2),
      Nat.cast_sub hh3]
      push_cast
      have hh4: ((m1:ℤ)^2-1)*((m2:ℤ)^2-1) = (m1*m2)^2 -
        (m1^2+m2^2-1) := by ring
      rw [hh4]
      linarith [hh1, hh2]
    apply h3.trans h4
  · -- now, consider n is prime power case.
    rcases h with ⟨p, k, pp, n_of_pk⟩
    -- since n > 1, we have k > 0.
    have kpos: 0 < k := by
      by_contra!
      replace: k = 0 := by exact eq_zero_of_le_zero this
      simp only [this, pow_zero] at n_of_pk
      simp [n_of_pk] at hn
    -- calculate σ (p^k) and φ (p^k)
    have h1: σ 1 (p^k) = ∑ i ∈ Finset.range (k+1), p^i := by
      apply sigma_one_apply_prime_pow pp
    have h2: φ (p^k) = p^(k-1) * (p-1) := by
      apply totient_prime_pow pp kpos
    qify
    -- notice that p^0+p^1+...+p^k = (p^(k+1)-1)/(p-1)
    have h3: (p:ℚ) - 1 ≠ 0 := by
      symm; apply _root_.ne_of_lt
      have: 1 < p := pp.one_lt
      qify at this; linarith [this]
    replace h1: (σ 1 (p^k): ℚ) = (p^(k+1) - 1)/(p-1) := by
      rw [h1]
      have := mul_geom_sum (p:ℚ) (k+1)
      push_cast
      rw [← this]; symm
      apply mul_div_cancel_left₀ _ h3
    qify at h2
    -- thereofre σ (p^k) φ (p^k) = (p^(k+1)-1) p^(k-1) = (p^k)^2 - p^(k-1)
    have h4: (↑(σ 1 n):ℚ) * φ (n) = n^2 - p^(k-1) := by
      rw [mul_comm] at h2
      rw [n_of_pk, h1, h2, ← mul_assoc, Nat.cast_sub (pp.one_le)]
      simp only [cast_one, isUnit_iff_ne_zero,
      ne_eq, h3, not_false_eq_true, IsUnit.div_mul_cancel, cast_pow]
      rw [sub_mul, one_mul]
      congr 1
      rw [← pow_add, ← pow_mul]
      congr 1
      omega
    -- p^(k-1) ≥ 1, done.
    have h5: 1 ≤ n^2 := one_le_pow _ _ (zero_lt_of_lt hn)
    have h6: (1:ℚ) ≤ (p:ℚ)^(k-1) := by
      norm_cast
      apply one_le_pow _ _ pp.pos
    rw [h4, Nat.cast_sub h5]
    push_cast
    linarith [h6]