import Mathlib

/- Rachelle picks a positive integer $a$ and writes it next to itself to obtain a new positive integer $b$.
For instance, if $a=17$, then $b=1717$. To her surprise, she finds that $b$ is a multiple of $a^{2}$.
Find the product of all the possible values of $\frac{b}{a^{2}}$. -/
theorem number_theory_608832:
  ∏ᶠ x ∈ {c:ℕ | ∃(a b:ℕ), 0 < a ∧ 0 < b ∧  a^2 ∣ b ∧
    Nat.digits 10 b = Nat.digits 10 a ++ Nat.digits 10 a ∧ c = b / a^2}, x = 77 := by

  -- by definition of b, b = a (10^k+1), where k is digits length of a.
  have h1 {a b:ℕ} (hb: Nat.digits 10 b = Nat.digits 10 a ++ Nat.digits 10 a):
    b = a * (10^(Nat.digits 10 a).length + 1) := by
    rw [← Nat.ofDigits_digits 10 b, hb, Nat.ofDigits_append,
    Nat.ofDigits_digits 10 a]
    ring

  -- and b ≠ a^2, since 10^(Nat.digits 10 a).length ≥ a.
  have bnea {a b:ℕ} (apos: 0 < a) (hb: Nat.digits 10 b = Nat.digits 10 a ++ Nat.digits 10 a):
    b ≠ a^2 := by
    rw [h1 hb, pow_two]
    rintro heq
    simp only [Nat.reduceLeDiff, ne_eq, apos.ne', not_false_eq_true,
    mul_eq_mul_left_iff, or_false] at heq
    have: 10^(Nat.digits 10 a).length > a := by
      exact Nat.lt_base_pow_length_digits'
    nth_rw 2 [← heq] at this
    simp at this

  -- thus a divide 10^k + 1
  have h2 {a b:ℕ} (hb1: Nat.digits 10 b = Nat.digits 10 a ++ Nat.digits 10 a)
    (hb2: a^2 ∣ b) (ha: 0 < a):
    a ∣ 10^(Nat.digits 10 a).length + 1 := by
    rcases hb2 with ⟨c, hc⟩
    use c
    rw [h1 hb1, pow_two, mul_assoc] at hc
    exact Nat.eq_of_mul_eq_mul_left ha hc

  -- notice that a ≥ 10^(k-1), or, 10a ≥ 10^k
  have h3 {a:ℕ} (ha: 0 < a): 10*a ≥ 10^(Nat.digits 10 a).length := by
    exact Nat.base_pow_length_digits_le _ _ (by norm_num) ha.ne'




  -- a divide 10^k+1, let c = (10^k+1)/a. then c ≤ (10^k+1)/10^(k-1) ≤ 11.
  have h4 {k c:ℕ} (cpos: 0 < c) (cdvd: c ∣ 10^k+1) (h: 10 * (10^k+1)/c ≥ 10^k):
    c ≤ 11 := by
    by_cases hk: k = 0
    · simp only [hk, pow_zero, Nat.reduceAdd] at cdvd
      replace cdvd := Nat.le_of_dvd (by norm_num) cdvd
      linarith only [cdvd]
    replace hk: 1 ≤ k := by omega
    replace h: 10 * (10^k+1) ≥ 10^k * c := by
      exact (Nat.le_div_iff_mul_le cpos).mp h
    replace h: c ≤ 10 * (10^k+1) / (10^k) := by
      refine (Nat.le_div_iff_mul_le (by simp)).mpr ?_
      rwa [mul_comm c _]
    apply le_trans h ?_
    have hh1: 10 * (10^k+1) ≤ 10 * (10^k + 10^(k-1)) := by
      refine Nat.mul_le_mul_left 10 ?_
      simp only [add_le_add_iff_left]
      exact Nat.one_le_pow' (k - 1) 9
    rw [mul_add 10 _ (10^(k-1)), ← pow_succ' _ (k-1),
    Nat.sub_add_cancel hk] at hh1
    have hh2: 10 * (10^k+1) / 10^k ≤ (10*10^k+10^k) / 10^k := by
      exact Nat.div_le_div_right hh1
    apply le_trans hh2 ?_
    simp

  -- for c ≤ 11 and divide 10^k+1, c can only be 7 or 11
  have h5 {c k:ℕ} (cpos: 0 < c) (cdvd: c ∣ 10^k+1) (h: 10 * (10^k+1)/c ≥ 10^k)
    (kpos: 0 < k): c = 1 ∨ c = 7 ∨ c = 11 := by

    -- 2,3,5 does not divide 10^k+1.
    have dvd2: ¬ 2 ∣ 10^k+1 := by
      by_contra! hh1
      have hh2: 2 ∣ 10^k := by
        refine Dvd.dvd.pow (by norm_num) kpos.ne'
      have hh3: 2 ∣ 1 := (Nat.dvd_add_iff_right hh2).mpr hh1
      norm_num at hh3
    have dvd3: ¬ 3 ∣ 10^k+1 := by
      by_contra! hh1
      replace hh1: 10^k+1 ≡ 0 [MOD 3] := by
        exact Nat.ModEq.symm (Dvd.dvd.zero_modEq_nat hh1)
      have hh2: 1 ≡ 1 [MOD 3] := rfl
      have hh3: 10^k ≡ 1 [MOD 3] := by
        have: 10^k ≡ 1^k [MOD 3] := by
          exact Nat.ModEq.pow k rfl
        rwa [one_pow] at this
      have hh4: 10^k+1 ≡ 1+1 [MOD 3] := by
        exact Nat.ModEq.add_right 1 hh3
      have hh5: 1+1 ≡ 0 [MOD 3] := by
        apply Nat.ModEq.trans hh4.symm hh1
      contradiction
    have dvd5: ¬ 5 ∣ 10^k+1 := by
      by_contra! hh1
      have hh2: 5 ∣ 10^k := by
        apply Dvd.dvd.pow (by norm_num) kpos.ne'
      have hh3: 5 ∣ 1 := (Nat.dvd_add_iff_right hh2).mpr hh1
      norm_num at hh3

    -- thus c cannot be divided by 2,3,5.
    have hc2: ¬ 2 ∣ c := by
      by_contra!
      absurd dvd2
      exact Nat.dvd_trans this cdvd
    have hc3: ¬ 3 ∣ c := by
      by_contra!
      absurd dvd3
      exact Nat.dvd_trans this cdvd
    have hc5: ¬ 5 ∣ c := by
      by_contra!
      absurd dvd5
      exact Nat.dvd_trans this cdvd

    -- so c can only be 1,7,11.
    specialize h4 cpos cdvd h
    clear * - hc2 hc3 hc5 h4
    revert hc2 hc3 hc5
    decide +revert

  -- and we find c=1 is impossible, thus elements in that set is 7,11.
  have h6: {c:ℕ | ∃(a b:ℕ), 0 < a ∧ 0 < b ∧  a^2 ∣ b ∧
    Nat.digits 10 b = Nat.digits 10 a ++ Nat.digits 10 a ∧ c = b / a^2} =
    {7,11} := by
    ext c
    simp only [exists_and_left, Set.mem_setOf_eq,
    Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨a, apos, b, bpos, hdvd, hba, hc⟩
      have hc': a^2*c = b := by
        exact (Nat.eq_mul_of_div_eq_right hdvd hc.symm).symm
      have cpos: 0 < c := by
        rw [← hc'] at bpos
        exact Nat.pos_of_mul_pos_left bpos
      have cne1: c ≠ 1 := by
        rintro rfl
        specialize bnea apos hba
        simp [← hc'] at bnea
      have cdvd: c ∣ b/a := by
        rw [← hc', pow_two]
        refine Nat.dvd_div_of_mul_dvd ?_
        rw [mul_assoc]
        exact Nat.dvd_mul_left (a * c) a
      rw [h1 hba, Nat.mul_div_right _ apos] at cdvd
      specialize h3 apos
      specialize h5 cpos cdvd
      simp only [cne1, false_or] at h5
      apply h5 ?_ ?_
      · have hh1: 10^(Nat.digits 10 a).length + 1 = b/a := by
          rw [h1 hba]
          field_simp [apos.ne']
        rw [hh1, ← hc', pow_two]
        have hh2: a*a*c/a = a*c := by
          refine Nat.div_eq_of_eq_mul_right apos ?_
          ring
        rwa [hh2, Nat.mul_div_assoc _ (Nat.dvd_mul_left c a),
        Nat.mul_div_left a cpos]
      · rw [Nat.digits_len _ _ (by norm_num) apos.ne']
        simp
    · -- verification 7,11 are possible solutions.
      -- we need find such a,b witness c.
      -- for example, a=1, a=143.
      rintro (rfl | rfl)
      · use 143
        refine ⟨(by norm_num), ?_⟩
        use 143143
        norm_num
      · use 1
        refine ⟨(by norm_num), ?_⟩
        use 11
        norm_num

  -- only possible c is 7 and 11, so product is 77.
  rw [h6, finprod_mem_pair (by norm_num)]
  norm_num