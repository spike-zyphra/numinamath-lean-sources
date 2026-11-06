import Mathlib


/- prime number has exactly two divisors -/
lemma l_prime_card_divisors {p:ℕ} (pp: Nat.Prime p):
  p.divisors.card = 2 := by
  rw [pp.divisors, Finset.card_pair]
  exact pp.one_lt.ne

/- any natural numbers > 1 has at least two divisors. -/
lemma l_two_le_card_divisors {a:ℕ} (ha0: a ≠ 0) (ha1: a ≠ 1):
  2 ≤ a.divisors.card := by
  have pa: Nat.Prime a.minFac := Nat.minFac_prime ha1
  have: a.minFac.divisors ⊆ a.divisors := by
    refine Nat.divisors_subset_of_dvd ha0 ?_
    exact Nat.minFac_dvd a
  replace: a.minFac.divisors.card ≤ a.divisors.card :=
    Finset.card_le_card this
  rwa [l_prime_card_divisors pa] at this

/- if pq ∣ n, p,q are distinct primes, then n is not prime power -/
lemma l_not_prime_pow_of_mul_dvd {n p q:ℕ} (h1: p*q ∣ n) (h2: p ≠ q)
  (pp: Nat.Prime p) (pq: Nat.Prime q): ¬ IsPrimePow n := by
  rw [isPrimePow_nat_iff]
  rintro ⟨r, k, pr, kpos, hn⟩
  have h3: p ∣ r := by
    have: p ∣ n := dvd_of_mul_right_dvd h1
    rw [← hn] at this
    exact pp.dvd_of_dvd_pow this
  have h4: q ∣ r := by
    have: q ∣ n := dvd_of_mul_left_dvd h1
    rw [← hn] at this
    apply pq.dvd_of_dvd_pow this
  rw [pr.dvd_iff_eq pp.ne_one] at h3
  rw [pr.dvd_iff_eq pq.ne_one] at h4
  simp [← h3, ← h4] at h2

/- if p is prime, a is not prime power, then number of divisors of ap ≥ that of a+2. -/
lemma l_card_divisors_add_two_le_mul_prime_card {a p: ℕ} (pp: Nat.Prime p) (ha0: a ≠ 0)
  (ha1: a ≠ 1) (hpa: ¬ IsPrimePow a): a.divisors.card + 2 ≤ (a*p).divisors.card := by
  by_cases hp: p ∣ a
  · have h1: a = p^(a.factorization p) * (a / p^(a.factorization p)) := by
      refine Nat.eq_mul_of_div_eq_right ?_ rfl
      exact Nat.ordProj_dvd a p
    have h2: Nat.Coprime (p^(a.factorization p)) (a / p^(a.factorization p)) := by
      refine Nat.Coprime.pow_left (a.factorization p) ?_
      exact Nat.coprime_ordCompl pp ha0
    have h2': Nat.Coprime (p^(a.factorization p + 1)) (a / p^(a.factorization p)) := by
      refine Nat.Coprime.pow_left _ ?_
      exact Nat.coprime_ordCompl pp ha0
    rw [h1]
    rw [mul_comm _ p, ← mul_assoc, ← pow_succ',
    h2.card_divisors_mul, h2'.card_divisors_mul]
    simp only [← ArithmeticFunction.sigma_zero_apply,
    ArithmeticFunction.sigma_apply_prime_pow pp,
    mul_zero, pow_zero, Finset.sum_const,
    Finset.card_range, smul_eq_mul, mul_one, ge_iff_le]
    nth_rw 2 [Nat.add_one_mul]
    simp only [add_le_add_iff_left, ArithmeticFunction.sigma_zero_apply]
    refine l_two_le_card_divisors ?_ ?_
    · have: p^(a.factorization p) ≠ 0 := by
        simp [pp.ne_zero]
      simp only [ne_eq, Nat.div_eq_zero_iff, this,
      false_or, not_lt, ge_iff_le]
      exact Nat.ordProj_le p ha0
    · by_contra!
      rw [this, mul_one] at h1
      absurd hpa
      rw [h1]
      use p,a.factorization p
      simp only [and_true]
      constructor
      · exact Nat.prime_iff.mp pp
      · exact pp.factorization_pos_of_dvd ha0 hp
  · have h1: 0 < a.divisors.card := by
      refine Finset.card_pos.mpr ?_
      exact Nat.nonempty_divisors.mpr ha0
    replace hp: Nat.Coprime a p := by
      refine Nat.coprime_comm.mp ?_
      exact (Nat.Prime.coprime_iff_not_dvd pp).mpr hp
    rw [hp.card_divisors_mul, l_prime_card_divisors pp, mul_two]
    simp only [add_le_add_iff_left, ge_iff_le]
    exact l_two_le_card_divisors ha0 ha1



/- Example 1 Let $p$ be a prime number, and the number of distinct positive divisors of
$p^{2}+71$ does not exceed 10. Find the value of $p$. -/
theorem number_theory_271677 {p: ℕ} (pp: Nat.Prime p):
  (p^2+71).divisors.card ≤ 10 ↔ (p = 2 ∨ p = 3) := by

  have: p^2+71 = (p-1)*(p+1) + 24*3 := by
    rw [mul_comm (p-1) _, ← Nat.sq_sub_sq]
    have: 1 ≤ p^2 := Nat.one_le_pow _ _ pp.pos
    simp [this]

  -- if p = 3k+1, k even, then p^2+71 is divided by 24
  have case_3k_1 {k:ℕ} (hk: Even k) (peq: p = 3*k + 1):
    24 ∣ p^2 + 71 := by
    rw [this, peq, add_tsub_cancel_right]
    have: 24 ∣ 3*k*(3*k+1+1) := by
      rw [even_iff_exists_two_mul] at hk
      rcases hk with ⟨m, hm⟩
      have h1: 3*k*(3*k+1+1) = 12*(m*(3*m + 1)) := by
        rw [hm]
        ring
      -- one of m, 3m+1 is even, has factor 2.
      have h2: Even (m * (3*m+1)) := by
        by_cases hm: Even m
        · apply hm.mul_right
        · replace hm: Even (3*m+1) := by
            rw [Nat.not_even_iff_odd] at hm
            replace hm: Odd (3*m) := by
              rw [mul_comm]
              apply hm.mul (Nat.odd_iff.mpr rfl)
            exact hm.add_one
          apply hm.mul_left
      rw [even_iff_exists_two_mul] at h2
      rcases h2 with ⟨mm, hmm⟩
      rw [h1, hmm, ← mul_assoc]
      simp only [Nat.reduceMul, dvd_mul_right]
    apply this.add (Nat.dvd_mul_right _ _)

  -- if p = 3k-1, k even, also 24 divide p^2+1
  have case_3k_neg1 {k:ℕ} (hk: Even k) (kpos: 0 < k)
    (peq: p = 3*k - 1): 24 ∣ p^2 + 71 := by
    rw [this, peq]
    replace: 1 ≤ 3*k := by omega
    simp only [this, Nat.sub_add_cancel]
    have: 24 ∣ (3*k-1-1)*(3*k) := by
      rw [even_iff_exists_two_mul] at hk
      rcases hk with ⟨m, hm⟩
      have h1: (3*k-1-1)*(3*k) = 12*(m*(3*m-1)) := by
        replace: 3*k - 1 - 1 = 3*k - 2 := by omega
        rw [this, hm]
        replace: 3*(2*m) - 2 = 2*(3*m - 1) := by
          rw [Nat.mul_sub_one, ← mul_assoc,
          mul_comm 3 2, mul_assoc]
        rw [this]
        ring
      have h2: Even (m*(3*m-1)) := by
        by_cases hhm: Even m
        · apply hhm.mul_right
        · rw [Nat.not_even_iff_odd] at hhm
          refine Even.mul_left ?_ _
          have: Odd (3*m) := by
            rw [mul_comm]
            apply hhm.mul (Nat.odd_iff.mpr rfl)
          refine Odd.tsub_odd this ?_
          exact Nat.odd_iff.mpr rfl
      rcases h2 with ⟨kk, hkk⟩
      rw [h1, hkk, ← two_mul, ← mul_assoc]
      simp only [Nat.reduceMul, dvd_mul_right]
    apply this.add (Nat.dvd_mul_right _ _)

  -- if p is prime, p mod 3 can only be 3k-1 or 3k+1 for even k.
  have h_mod (hp: p > 3): (∃ (k:ℕ), Even k ∧ p = 3*k - 1) ∨
    (∃ k, Even k ∧ p = 3*k + 1) := by
    mod_cases h: p % 3
    · rw [Nat.modEq_zero_iff_dvd] at h
      rw [pp.dvd_iff_eq (by norm_num)] at h
      simp [h] at hp
    · symm at h
      rw [Nat.modEq_iff_dvd' pp.one_le] at h
      rcases h with ⟨k, hk⟩
      replace hk: p = 3*k + 1 := by
        refine (Nat.sub_eq_iff_eq_add pp.one_le).mp hk
      -- k must be even, otherwise p is even.
      right
      refine ⟨k, ?_, hk⟩
      by_contra!
      rw [Nat.not_even_iff_odd] at this
      replace: Odd (3*k) := by
        refine Nat.odd_mul.mpr ⟨?_, this⟩
        exact Nat.odd_iff.mpr rfl
      replace: Even p := by
        rw [hk]
        exact Odd.add_one this
      rw [pp.even_iff] at this
      simp [this] at hp
    · symm at h
      rw [Nat.modEq_iff_dvd' pp.two_le] at h
      rcases h with ⟨k, hk⟩
      replace hk: p = 3*k + 2 := by
        refine (Nat.sub_eq_iff_eq_add pp.two_le).mp hk
      replace hk: p = 3*(k+1) - 1 := by
        rw [hk, Nat.mul_add_one]
        simp
      -- k+1 is even, otherwise 3(k+1) - 1 is even.
      left
      refine ⟨(k+1), ?_, hk⟩
      by_contra!
      rw [Nat.not_even_iff_odd] at this
      replace: Odd (3*(k+1)) := by
        refine Nat.odd_mul.mpr ⟨?_, this⟩
        exact Nat.odd_iff.mpr rfl
      replace: Even p := by
        rw [hk]
        refine Odd.tsub_odd this ?_
        exact Nat.odd_iff.mpr rfl
      rw [pp.even_iff] at this
      simp [this] at hp

  -- if 24 divide n, number of divisors of n > 10
  have h_card {n:ℕ} (hn1: 24 ∣ n) (hn2: n > 24 * 3):
    n.divisors.card > 10 := by
    rcases hn1 with ⟨k, rfl⟩
    replace hn2: k > 3 := Nat.lt_of_mul_lt_mul_left hn2
    replace hn2: k ≥ 4 := by exact hn2
    have := Nat.minFac_dvd k
    rcases this with ⟨q, hq⟩
    have h1: (24*k.minFac*q.minFac).divisors ⊆ (24*k).divisors := by
      refine Nat.divisors_subset_of_dvd (by omega) ?_
      nth_rw 2 [hq]
      rw [← mul_assoc]
      refine Nat.mul_dvd_mul_left (24 * k.minFac) ?_
      exact Nat.minFac_dvd q
    suffices (24*k.minFac*q.minFac).divisors.card > 10 by
      apply lt_of_lt_of_le this ?_
      exact Finset.card_le_card h1
    have co_23: Nat.Coprime 2 3 := by norm_num
    have pk: Nat.Prime k.minFac := by
      refine Nat.minFac_prime ?_
      omega
    by_cases hhq: q = 1
    · -- if q = 1, k itself is prime. it ≥ 4, so distinct from 2,3.
      rw [hhq, mul_one] at hq
      have hk2: k.minFac ≠ 2 := by
        rintro heq
        rw [heq] at hq
        simp [hq] at hn2
      have hk3: k.minFac ≠ 3 := by
        rintro heq
        rw [heq] at hq
        simp [hq] at hn2
      rw [← Nat.coprime_primes pk (by norm_num)] at hk2 hk3
      have co_k23: Nat.Coprime (2^3 * 3^1) k.minFac := by
        refine Nat.coprime_mul_iff_left.mpr ?_
        constructor <;> refine Nat.Coprime.pow_left _ ?_
        · exact hk2.symm
        · exact hk3.symm
      have: 24 * k.minFac * q.minFac = 2^3 * 3^1 * k.minFac := by
        simp [hhq]
      rw [this, co_k23.card_divisors_mul]
      rw [l_prime_card_divisors pk]
      -- divisors card is (3+1) x (1+1) x 2 = 4 x 2 x 2 > 10
      decide
    · -- we show number of divisors of 24 k.minFac ≥ 10.
      -- therefore it multiply q > 10.
      suffices (24*k.minFac).divisors.card ≥ 10 by
        apply lt_of_le_of_lt this ?_
        replace: (24*k.minFac).divisors.card + 2 ≤
          (24*k.minFac*q.minFac).divisors.card := by
          refine l_card_divisors_add_two_le_mul_prime_card ?_ ?_ ?_ ?_
          · exact Nat.minFac_prime hhq
          · simp [pk.ne_zero]
          · simp
          · apply @l_not_prime_pow_of_mul_dvd _ 2 3
              (Dvd.dvd.mul_right ?_ _) ?_ ?_ ?_
            <;> norm_num
        apply lt_of_lt_of_le ?_ this
        simp
      have h1: (Nat.divisors 24).card = 8 := by
        -- number of divisors of 24 = 2^3 x 3^1 is (3+1) x (1+1) = 8.
        decide
      have h2: (Nat.divisors 24).card + 2 ≤ (24*k.minFac).divisors.card := by
        refine l_card_divisors_add_two_le_mul_prime_card pk ?_ ?_ ?_
        any_goals norm_num
        -- 24 is not prime power.
        decide
      norm_num [h1] at h2
      exact h2

  -- therefore suffices to show p^2+71 not divided by 24 iff p = 2 or 3.

  constructor
  · intro h
    -- suffices to show impossible for p > 3
    suffices ¬ p > 3 by
      push_neg at this
      clear * - this pp
      revert pp
      decide +revert
    rintro pgt
    absurd h
    push_neg
    apply h_card ?_ ?_
    · rcases (h_mod pgt) with hh | hh
      · rcases hh with ⟨k, hk, hp⟩
        apply case_3k_neg1 hk ?_ hp
        rw [hp] at pgt
        omega
      · rcases hh with ⟨k, hk, hp⟩
        apply case_3k_1 hk hp
    · have: 1 < p^2 := by
        apply Nat.one_lt_pow (by norm_num) pp.one_lt
      linarith only [this]
  · -- verification
    -- p = 2, p^2+71 = 75. p = 3, p^2+71 = 80.
    -- divisor number of 75 = 5^2 x 3 is (2+1) x (1+1) = 6.
    -- divisor number of 80 = 2^4 x 5 is (4+1) x (1+1) = 10.
    -- both ≤ 10
    rintro (rfl | rfl)
    <;> decide