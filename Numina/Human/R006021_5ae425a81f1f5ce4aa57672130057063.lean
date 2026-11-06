import Mathlib


open ArithmeticFunction


/- A positive integer will be called "sparkly"
if its smallest (positive) divisor, other than 1, equals the total number of divisors (including 1).
How many of the numbers $2,3, \ldots, 2003$ are sparkly? -/
theorem number_theory_611152 {sparkly: ℕ → Prop}
  (sparkly_def: ∀n, sparkly n ↔
    (n.divisors.erase 1).min = n.divisors.card):
  {n:ℕ | 2 ≤ n ∧ n ≤ 2003 ∧ sparkly n}.ncard = 3 := by

  -- we claim smallest positive divisor of n other than 1 is its minimum prime factor.
  have h_minfac {n:ℕ} (hn: n ≥ 2): (n.divisors.erase 1).min = n.minFac := by
    have h1: n.minFac ∈ n.divisors.erase 1 := by
      refine Finset.mem_erase_of_ne_of_mem ?_ ?_
      · simp only [ne_eq, Nat.minFac_eq_one_iff]
        omega
      · refine Nat.mem_divisors.mpr ⟨?_, (by omega)⟩
        exact Nat.minFac_dvd n
    -- suppose b is its minimum.
    rcases (Finset.min_of_nonempty
      (Finset.nonempty_iff_ne_empty.mpr
        (Finset.ne_empty_of_mem h1))) with ⟨b,hb⟩
    -- then we claim b is minimum prime factor of n.
    have h2: b ≤ n.minFac := by
      exact Finset.min_le_of_eq h1 hb
    have h3: n.minFac ≤ b := by
      have hhb := Finset.mem_of_min hb
      refine Nat.minFac_le_of_dvd ?_ ?_
      · have hb0: b ≠ 0 := by
          rintro rfl
          simp at hhb
        have hb1: b ≠ 1 := by
          rintro rfl
          simp at hhb
        omega
      · have: b ∈ n.divisors := Finset.mem_of_mem_erase hhb
        exact Nat.dvd_of_mem_divisors this
    have: b = n.minFac := le_antisymm h2 h3
    rewrite [hb, this]
    rfl

  -- if n is divided by some prime q, then its divisors cardinal contain some factor related to q.
  have h_divisor_card {n p:ℕ} (hn: n ≥ 2) (pp: Nat.Prime p) (hp: p ∣ n):
    (n.factorization p + 1) ∣ n.divisors.card := by
    have h1: n.divisors.card = σ 0 n := by simp [sigma_zero_apply]
    have h2: n = p^(n.factorization p) * (n / p^(n.factorization p)) := by
      exact (Nat.ordProj_mul_ordCompl_eq_self n p).symm
    have h3: Nat.Coprime (p^(n.factorization p)) (n / p^(n.factorization p)) := by
      refine Nat.Coprime.pow_left (n.factorization p) ?_
      refine Nat.coprime_ordCompl pp (by omega)
    have h4 := @isMultiplicative_sigma 0
    rw [IsMultiplicative] at h4
    rw [h1]
    nth_rw 2 [h2]
    rw [h4.right h3, sigma_zero_apply_prime_pow pp]
    apply Nat.dvd_mul_right

  -- prime number cannot contain two factors > 1.
  have prime_irr {p q1 q2:ℕ} (hq1: q1 > 1) (hq2: q2 > 1)
    (pp: Nat.Prime p):
    ¬ q1*q2 ∣ p := by
    by_contra! hdvd
    have h1: q1 ∣ p := by
      exact dvd_of_mul_right_dvd hdvd
    have h2: q2 ∣ p := by
      exact dvd_of_mul_left_dvd hdvd
    rw [pp.dvd_iff_eq hq1.ne'] at h1
    rw [pp.dvd_iff_eq hq2.ne'] at h2
    rw [← h1, ← h2] at hdvd
    have h3: p*p ≤ p := Nat.le_of_dvd pp.pos hdvd
    have h4: p*2 ≤ p*p := Nat.mul_le_mul_left p pp.two_le
    replace h4 := h4.trans h3
    absurd h4
    push_neg
    linarith only [pp.pos]


  -- if n is sparkly, then n cannot contain more than one prime factor.
  have h_sparkly {n:ℕ} (hn1: n ≥ 2) (hn2: sparkly n):
    ∃ (i:ℕ), n = n.minFac^i := by
    have h1: n.minFac ≠ 1 := by
      simp only [ne_eq, Nat.minFac_eq_one_iff]
      omega
    have h2: n ≠ 0 := by omega
    rcases (Nat.exists_eq_pow_mul_and_not_dvd h2 n.minFac h1) with
      ⟨i, m, hm, heq⟩
    -- i ≠ 0, otherwise n = m, contradiction to n.minfac not divide m
    have inz: i ≠ 0 := by
      rintro rfl
      simp only [pow_zero, one_mul] at heq
      rw [← heq] at hm
      absurd hm
      exact Nat.minFac_dvd n
    use i
    have mnz: m ≠ 0 := by
      rintro rfl
      rw [heq] at h2
      simp at h2
    -- if m = 1, done.
    by_cases hm1: m = 1
    · nth_rw 1 [heq, hm1, mul_one]
    -- else, m contain prime factor
    have pm: Nat.Prime m.minFac := by
      exact Nat.minFac_prime hm1
    -- number of divisors of m has a factor
    have h3: m ≥ 2 := by omega
    replace h3 := h_divisor_card h3 pm (Nat.minFac_dvd m)
    -- number of divisors of n.minfac^i again has a factor
    have pn: Nat.Prime n.minFac := by
      refine Nat.minFac_prime (by omega)
    have hhn: n.minFac^i ≥ 2 := by
      have: n.minFac^i ≥ n.minFac := Nat.le_self_pow inz n.minFac
      linarith only [this, pn.two_le]
    have h4: n.minFac ∣ n.minFac^i := by
      exact dvd_pow_self n.minFac inz
    replace h4 := h_divisor_card hhn pn h4
    -- then we claim number of divisors of n has two factors.
    have h5: (m.factorization m.minFac + 1) *
      (n.factorization n.minFac + 1) ∣ n.divisors.card := by
      have co: Nat.Coprime n.minFac m := by
        exact (Nat.Prime.coprime_iff_not_dvd pn).mpr hm
      have co' := (Nat.Coprime.pow_left i co)
      have: n.divisors.card = m.divisors.card *
        (n.minFac^i).divisors.card := by
        simp only [← sigma_zero_apply]
        nth_rw 1 [heq]
        have := @isMultiplicative_sigma 0
        rw [IsMultiplicative] at this
        rw [this.right co', mul_comm]
      rw [this]
      refine Nat.mul_dvd_mul h3 ?_
      replace: n.factorization n.minFac =
        (n.minFac^i).factorization n.minFac := by
        nth_rw 1 [heq]
        rw [Nat.factorization_mul_of_coprime co']
        simp [Nat.factorization_eq_zero_of_not_dvd hm, inz]
      rwa [this]
    -- but if n is sparkly, its number of divisors is prime, contradiction.
    rw [sparkly_def, h_minfac hn1] at hn2
    norm_cast at hn2
    absurd h5
    rw [← hn2]
    apply prime_irr ?_ ?_ pn
    · have: 1 ≤ m.factorization m.minFac := by
        rw [← pm.dvd_iff_one_le_factorization mnz]
        exact Nat.minFac_dvd m
      omega
    · have: 1 ≤ n.factorization n.minFac := by
        rw [← pn.dvd_iff_one_le_factorization h2]
        exact Nat.minFac_dvd n
      omega

  -- so sparkly number must be of the form p^(p-1)
  replace h_sparkly {n:ℕ} (hn: n ≥ 2)
    (hs: sparkly n): ∃ (p:ℕ), Nat.Prime p ∧ n = p^(p-1) := by
    obtain ⟨i, hi⟩ := h_sparkly hn hs
    rw [sparkly_def, h_minfac hn] at hs
    norm_cast at hs
    nth_rw 2 [hi] at hs
    have pp: Nat.Prime n.minFac := by
      exact Nat.minFac_prime (by omega)
    have: (n.minFac ^ i).divisors.card = i+1 := by
      simp only [← sigma_zero_apply, sigma_zero_apply_prime_pow pp]
    rw [this] at hs
    replace hs: i = n.minFac - 1 := by
      simp [hs]
    use n.minFac
    refine ⟨pp, ?_⟩
    nth_rw 1 [hi, hs]

  -- then the set only contain three elements, 2^1, 3^2, 5^4,
  -- since 7^6 exceed 2003
  have: {n:ℕ | 2 ≤ n ∧ n ≤ 2003 ∧ sparkly n} =
    {2^1, 3^2, 5^4} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨nge, nle, hn⟩
      obtain ⟨p, pp, heq⟩ := h_sparkly nge hn
      -- p < 7, otherwise 7^6 > 2003
      have plt: p < 7 := by
        by_contra!
        have h1: p^(p-1) ≥ p^6 := by
          apply (Nat.pow_le_pow_iff_right pp.one_lt).mpr (by omega)
        have h2: p^6 ≥ 7^6 := by
          apply (Nat.pow_le_pow_iff_left (by norm_num)).mpr this
        rw [heq] at nle
        replace := (h2.trans h1).trans nle
        norm_num at this
      -- then p = 2,3,5
      obtain (hp | hp | hp): p=2 ∨ p=3 ∨ p=5 := by
        clear * - pp plt
        revert pp
        decide +revert
      all_goals norm_num [heq, hp]
    · rintro (hn | hn | hn)
      all_goals
        have nge: n ≥ 2 := by
          norm_num [hn]
        rw [sparkly_def, h_minfac nge]
        norm_cast
        simp only [← sigma_zero_apply]
        nth_rw 4 [hn]
        rw [sigma_zero_apply_prime_pow (by norm_num)]
        norm_num [hn]

  -- so answer is 3
  norm_num [this]