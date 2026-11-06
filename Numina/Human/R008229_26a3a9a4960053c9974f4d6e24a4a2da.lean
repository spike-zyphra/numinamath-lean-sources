import Mathlib

/- Soit $p$ et $q$ deux nombres premiers distincts, tels que $p<2 q$ et $q<2 p$.
Démontrer qu'il existe deux entiers consécutifs dont l'un a $p$ pour plus grand facteur premier et l'autre a $q$ pour plus grand facteur premier. -/
theorem number_theory_605182 (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (hpq : p < 2 * q) (hqp : q < 2 * p) :
    ∃ k, k > 0 ∧ ( ( (Nat.primeFactors k).max = p ∧
      (Nat.primeFactors (k + 1)).max = q  ) ∨
      ( (Nat.primeFactors k).max = q ∧
      (Nat.primeFactors (k + 1)).max = p ) )  := by

  -- by Bezout's theorem, exist a,b, such that ap + bq = 1
  have lemma_bezout: ∃ (a b: ℤ), a*p + b*q = 1 := by
    have h1: (p:ℤ).gcd (q:ℤ) = 1 := by
      exact (Nat.coprime_primes hp hq).mpr hne
    have h2 := Int.gcd_eq_gcd_ab p q
    simp only [h1, Nat.cast_one] at h2
    rw [h2]
    use ((p:ℤ).gcdA q),((p:ℤ).gcdB q)
    ring

  -- exist a, such that ap+bq = 1 and |a| ≤ |a-q|, |a| ≤ |a+q|
  replace lemma_bezout: ∃ (a b: ℤ), a*p + b*q = 1 ∧
    |a| ≤ |a-q| ∧ |a| ≤ |a+q| := by
    rcases lemma_bezout with ⟨a, b, heq⟩
    -- on cases a mod q is smaller or q - a mod q is smaller
    -- use one of them
    -- we can always find a "smallest" a.
    -- this is because if ap+bq = 1, then (a-nq)p + (b+np)q = 1.
    -- therefore we can always set a to a small value we want.
    have qpos: (0:ℤ) < q := by simp [hq.pos]
    by_cases ha: 0 ≤ a
    · have h1: a = (a.natAbs % q) + a / q * q := by
        nth_rw 1 [← Int.natAbs_of_nonneg ha]
        nth_rw 3 [← Int.natAbs_of_nonneg ha]
        norm_cast
        exact Eq.symm (Nat.mod_add_div' a.natAbs q)
      have h2: a = -(q - a.natAbs % q) + (a/q+1)*q := by
        nth_rw 1 [h1]
        ring
      by_cases h3: |a| % q ≤ q - |a| % q
      · use (a.natAbs % q)
        rw [h1] at heq
        use (b + a/q*p)
        refine ⟨?_, ?_, ?_⟩
        · rw [← heq]
          ring
        · rw [abs_sub_comm]
          simp only [Int.natCast_natAbs]
          refine abs_le_abs_of_nonneg ?_ h3
          apply Int.emod_nonneg _ (by simp [hq.ne_zero])
        · simp only [Int.natCast_natAbs]
          apply abs_le_abs_of_nonneg ?_ (by simp)
          apply Int.emod_nonneg _ (by simp [hq.ne_zero])
      · push_neg at h3
        use -(q - a.natAbs % q)
        rw [h2] at heq
        use (b + (a/q + 1)*p)
        refine ⟨?_, ?_, ?_⟩
        · nth_rw 2 [← heq]
          ring
        · simp only [Int.natCast_natAbs, neg_sub]
          nth_rw 1 [abs_sub_comm]
          have: |a| % q - q - q = - (q - |a| % q + q) := by ring
          rw [this, abs_neg]
          apply abs_le_abs_of_nonneg ?_ (by simp)
          linarith only [Int.emod_lt_of_pos |a| qpos]
        · simp only [Int.natCast_natAbs, neg_sub, sub_add_cancel]
          rw [abs_sub_comm]
          apply abs_le_abs_of_nonneg ?_ (le_of_lt h3)
          linarith only [Int.emod_lt_of_pos |a| qpos]
    · push_neg at ha
      have h1: -a = (a.natAbs % q) + -a / q * q := by
        replace ha := le_of_lt ha
        nth_rw 1 [← Int.ofNat_natAbs_of_nonpos ha]
        nth_rw 1 [← Int.ofNat_natAbs_of_nonpos ha]
        norm_cast
        exact Eq.symm (Nat.mod_add_div' a.natAbs q)
      have h2: -a = -(q - a.natAbs % q) + (-a/q+1)*q := by
        nth_rw 1 [h1]
        ring
      replace h1: a = -(a.natAbs % q) - -a/q * q := by
        have: a = - -a := by simp
        nth_rw 1 [this, h1]
        ring
      replace h2: a = (q - a.natAbs % q) - (-a/q+1)*q := by
        have: a = - -a := by simp
        nth_rw 1 [this, h2]
        ring
      by_cases h3: |a| % q ≤ q - |a| % q
      · rw [h1] at heq
        use (- (a.natAbs % q))
        use (b - -a/q * p)
        refine ⟨?_, ?_, ?_⟩
        · rw [← heq]
          ring
        · simp only [Int.natCast_natAbs, abs_neg]
          have: - (|a| % q) - q = - (|a| % q + q) := by ring
          rw [this, abs_neg]
          apply abs_le_abs_of_nonneg ?_ (by simp)
          exact Int.emod_nonneg |a| qpos.ne'
        · simp only [Int.natCast_natAbs, abs_neg]
          rw [neg_add_eq_sub]
          apply abs_le_abs_of_nonneg ?_ h3
          exact Int.emod_nonneg _ qpos.ne'
      · push_neg at h3
        rw [h2] at heq
        use (q - a.natAbs % q)
        use (b - (-a/q+1)*p)
        refine ⟨?_, ?_, ?_⟩
        · nth_rw 2 [← heq]
          ring
        · simp only [Int.natCast_natAbs, sub_sub_cancel_left, abs_neg]
          apply abs_le_abs_of_nonneg ?_ (le_of_lt h3)
          linarith only [Int.emod_lt_of_pos |a| qpos]
        · simp only [Int.natCast_natAbs]
          apply abs_le_abs_of_nonneg ?_ (by simp)
          linarith only [Int.emod_lt_of_pos |a| qpos]

  rcases lemma_bezout with ⟨a, b, heq, ha1, ha2⟩
  -- such a,b cannot be 0.
  have anz: a ≠ 0 := by
    rintro rfl
    simp only [zero_mul, zero_add] at heq
    have: (q:ℤ) ≤ 1 := by
      apply Int.le_of_dvd (by norm_num) ?_
      rw [← heq]
      exact Int.dvd_mul_left b _
    linarith only [this, hq.one_lt]
  have bnz: b ≠ 0 := by
    rintro rfl
    simp only [zero_mul, add_zero] at heq
    have: (p:ℤ) ≤ 1 := by
      apply Int.le_of_dvd (by norm_num) ?_
      rw [← heq]
      exact Int.dvd_mul_left a _
    linarith only [this, hp.one_lt]

  -- simplify these inequalities, |a| ≤ 2q
  have haq: 2*|a| ≤ q := by
    by_cases ha: 0 < a
    · rw [abs_of_pos ha] at ha1 ⊢
      rw [le_abs] at ha1
      rcases ha1 with ha1 | ha1
      · simp [hq.ne_zero] at ha1
      · linarith only [ha1]
    · push_neg at ha
      rw [abs_of_nonpos ha] at ha2 ⊢
      rw [le_abs] at ha2
      rcases ha2 with ha2 | ha2
      · linarith only [ha2]
      · simp [hq.ne_zero] at ha2
  -- also, 2*|b| ≤ p+1
  have hbp: 2*|b| ≤ p+1 := by
    replace heq: 2*b*q = 2 - 2*a*p := by
      linarith only [heq]
    have h1: (2*|b|)*q = |2*b*q| := by
      simp only [abs_mul, Nat.abs_ofNat, Nat.abs_cast]
    have h2: |2-2*a*p| ≤ (2*|a|)*p + 2:= by
      have: |2 - 2*a*p| ≤ |2| + |2*a*p| := abs_sub _ _
      apply this.trans (le_of_eq ?_)
      simp only [Nat.abs_ofNat, abs_mul, Nat.abs_cast, add_comm]
    have h3: (2*|b|)*q ≤ (p+1)*q := calc
      (2*|b|)*q ≤ (2*|a|)*p + 2 := by
        rwa [h1, heq]
      _ ≤ (2*|a|)*p + q := by
        linarith only [hq.two_le]
      _ ≤ q*p + q := by
        simp only [add_le_add_iff_right]
        exact Int.mul_le_mul_of_nonneg_right haq (by simp)
      _ = _ := by ring
    exact Int.le_of_mul_le_mul_right h3 (by simp [hq.pos])

  -- therefore a < p and b ≤ q
  have hap: |a| < p := by
    have: 2*|a| < 2*p := by
      apply lt_of_le_of_lt haq ?_
      norm_cast
    exact lt_of_nsmul_lt_nsmul_right 2 this
  have hbq: |b| ≤ q := by
    have: 2*|b| ≤ 2*q := by
      apply le_trans hbp ?_
      have: p+1 ≤ 2*q := by exact hpq
      norm_cast
    apply le_of_mul_le_mul_left this (by norm_num)

  -- notice that max prime factor of cr is r,
  -- if c ≤ r and r is a prime number.
  have max_prime_fac {c r: ℕ} (hr: Nat.Prime r) (hc1: c ≤ r) (hc2: 0 < c):
    (c*r).primeFactors.max = r := by
    rw [Nat.primeFactors_mul hc2.ne' hr.ne_zero]
    rw [Finset.max_union]
    apply le_antisymm
    · rw [max_le_iff]
      constructor
      · rw [Finset.max_le_iff]
        intro n
        simp only [Nat.mem_primeFactors, ne_eq, and_imp]
        intro pn ndvd _
        have := Nat.le_of_dvd hc2 ndvd
        replace := le_trans this hc1
        exact (WithBot.coe_le rfl).mpr this
      · simp only [hr.primeFactors, Finset.max_singleton]
        rfl
    · rw [le_max_iff]; right
      simp only [hr.primeFactors, Finset.max_singleton]
      rfl

  -- thus we claim |a|p and |b|q are the very two consecutive numbers.

  have hb: b*q = 1 - a*p := by linarith only [heq]

  by_cases ha: a < 0
  · -- if a < 0, |a|p + 1 = bq.
    have: a.natAbs*p + 1 = b.natAbs * q := by
      zify
      rw [← heq]
      replace hb: 0 < b := by
        have: 0 < b*q := by
          rw [hb]
          nlinarith only [ha, hp.pos]
        apply pos_of_mul_pos_left this (by simp)
      rw [abs_of_neg ha, abs_of_pos hb]
      ring
    -- use |a|p.
    use a.natAbs*p
    rw [this]
    constructor
    · simp [hp.pos, anz]
    · left; constructor
      · apply max_prime_fac hp ?_ (by simp [anz])
        zify
        apply le_of_lt hap
      · apply max_prime_fac hq ?_ (by simp [bnz])
        zify
        exact hbq
  · -- if a ≥ 0, ap = -bq+1
    push_neg at ha
    -- b < 0 when a > 0
    replace hb: b < 0 := by
      have: b*q < 0 := by
        rw [hb]
        replace ha: a ≥ 1 := by
          have := lt_of_le_of_ne ha anz.symm
          exact this
        nlinarith only [ha, hp.two_le]
      apply neg_of_mul_neg_left this (by simp)
    -- |b|q+1 = |a|p
    have: a.natAbs * p = b.natAbs * q + 1 := by
      zify
      simp only [abs_of_nonneg ha, abs_of_neg hb]
      linarith only [heq]
    -- use |b|q
    use b.natAbs*q;
    rw [← this]
    refine ⟨?_, ?_⟩
    · simp [hq.pos, bnz]
    · right; constructor
      · apply max_prime_fac hq ?_ (by simp [bnz])
        zify; exact hbq
      · apply max_prime_fac hp ?_ (by simp [anz])
        zify
        apply le_of_lt hap