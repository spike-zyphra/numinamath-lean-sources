import Mathlib


/- if n > 3 and n is odd, then more than 2 numbers < n and coprime to n -/
lemma l_two_lt_totient_of_odd_of_three_lt {n:ℕ} (hn1: ¬ 2 ∣ n) (hn2: n > 3):
  2 < n.totient := by
  rw [Nat.totient_eq_card_lt_and_coprime]
  have h1: {1,2,4} ⊆ {m | m < n ∧ n.Coprime m} := by
    intro m
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_setOf_eq]
    have p2: Nat.Prime 2 := by norm_num
    rintro (meq | meq | meq)
    <;> rw [meq]
    · refine ⟨(by omega), ?_⟩
      exact Nat.gcd_one_right n
    · refine ⟨(by omega), ?_⟩
      rw [← p2.coprime_iff_not_dvd] at hn1
      exact hn1.symm
    · refine ⟨(by omega), ?_⟩
      have: 4 = 2^2 := by norm_num
      rw [this]
      apply p2.coprime_pow_of_not_dvd hn1
  have h2: Nat.card ↑({1,2,4}: Set ℕ) = 3 := by
    norm_num
  change 3 ≤ Nat.card {m | m < n ∧ n.Coprime m}
  rw [← h2]
  apply Nat.card_mono ?_ h1
  have hh1: {m | m < n ∧ n.Coprime m} ⊆ Finset.range n := by
    intro m
    simp only [Set.mem_setOf_eq,
    Finset.coe_range, Set.mem_Iio, and_imp]
    tauto
  have hh2: (↑(Finset.range n): Set ℕ).Finite := by
    exact Finset.finite_toSet (Finset.range n)
  exact Set.Finite.subset hh2 hh1


/- if n > 2, then at least 2 numbers < n and coprime to n -/
lemma l_two_le_totient_of_lt_two {n : ℕ} (hn: 2 < n):
  n.totient ≥ 2 := by
  have h1: 0 < n.totient := by
    refine Nat.totient_pos.mpr ?_
    omega
  have h2: n.totient ≠ 1 := by
    rintro h2
    rw [Nat.totient_eq_one_iff] at h2
    omega
  omega

/- if n > 6, then more than 2 numbers < n and coprime to n.  -/
lemma l_two_lt_totient_of_six_lt {n : ℕ} (hn : n > 6):
  2 < n.totient := by
  by_cases hpn: Nat.Prime n
  · rw [Nat.totient_prime hpn]
    omega
  have pn: Nat.Prime n.minFac := by
    refine Nat.minFac_prime ?_
    omega
  have h1: n = n.minFac * (n / n.minFac) := by
    refine Eq.symm (Nat.mul_div_cancel' ?_)
    exact Nat.minFac_dvd n
  have h2: (n / n.minFac) > 2 := by
    apply lt_of_le_of_ne ?_ ?_
    · have: n.minFac ≤ (n / n.minFac) := Nat.minFac_le_div (by omega) hpn
      exact pn.two_le.trans this
    · rintro heq
      have: n.minFac = 2 := by
        apply le_antisymm ?_ pn.two_le
        rw [heq]
        apply Nat.minFac_le_div (by omega) hpn
      rw [← heq, this] at h1
      norm_num [h1] at hn
  by_cases h3: n.minFac = 2
  · by_cases h4: 2 ∣ (n / n.minFac)
    · replace h4: 4 ∣ n := by
        have: 4 = 2*2 := by norm_num
        rw [h1, this]
        rw [h3] at h4 ⊢
        exact Nat.mul_dvd_mul_left 2 h4
      rcases h4 with ⟨m, hm⟩
      have mge: m ≥ 2 := by omega
      by_cases hhm: m = 2
      · rw [hm, hhm]
        native_decide
      · replace hhm: m > 2 := by omega
        have hh1: Nat.totient 4 = 2 := by native_decide
        have hh2 := Nat.totient_super_multiplicative 4 m
        have hh3 := l_two_le_totient_of_lt_two hhm
        rw [← hm, hh1] at hh2
        linarith only [hh2, hh3]
    · suffices 2 < (n / n.minFac).totient by
        have hh := Nat.totient_super_multiplicative (n.minFac) (n / n.minFac)
        rw [h1]
        apply lt_of_lt_of_le ?_ hh
        refine lt_mul_of_one_le_of_lt ?_ this
        simp only [h3, Nat.totient_two, le_refl]
      apply l_two_lt_totient_of_odd_of_three_lt h4 ?_
      suffices n / n.minFac ≠ 3 by omega
      rintro h5
      rw [h1, h5, h3] at hn
      norm_num at hn
  · replace h3: n.minFac > 2 := by
      apply lt_of_le_of_ne pn.two_le ?_
      symm; exact h3
    have h4: n.minFac.totient * (n / n.minFac).totient ≥ 2*2 := by
      have hh1 := l_two_le_totient_of_lt_two h3
      have hh2 := l_two_le_totient_of_lt_two h2
      exact Nat.mul_le_mul hh1 hh2
    have h5 := Nat.totient_super_multiplicative (n.minFac) (n / n.minFac)
    rw [← h1] at h5
    linarith only [h4,h5]


/- 3 divide 2^n + 1 for odd n -/
lemma l_three_dvd_two_odd_pow_add_one {n : ℕ} (hn : Odd n):
  3 ∣ 2^n + 1 := by
  suffices 2^n ≡ -1 [ZMOD 3] by
    zify
    rw [← Int.modEq_zero_iff_dvd]
    refine Dvd.dvd.modEq_zero_int ?_
    symm at this
    rwa [Int.modEq_iff_dvd] at this
  have: 2 ≡ -1 [ZMOD 3] := rfl
  replace := this.pow n
  rwa [hn.neg_one_pow] at this

/- 3 not divide 2^n+1 for even n -/
lemma l_three_not_dvd_two_even_pow_add_one {n : ℕ} (hn : Even n):
  ¬ 3 ∣ 2^n + 1 := by
  suffices 2^n ≡ 1 [ZMOD 3] by
    zify
    symm at this
    rw [Int.modEq_iff_dvd] at this
    by_contra! hh
    replace: (3:ℤ) ∣ (2^n+1) - (2^n - 1) := Int.dvd_sub hh this
    norm_num at this
  have: 2 ≡ -1 [ZMOD 3] := rfl
  replace := this.pow n
  rwa [hn.neg_one_pow] at this

/- 16. (ROM 1) ${ }^{\mathrm{IMO} 2}$ Let $n>6$ and $a_{1} < a_{2} < \cdots < a_{k}$ be all natural numbers that are less than $n$ and relatively prime to $n$. Show that if $a_{1}, a_{2}, \ldots, a_{k}$ is an arithmetic progression, then $n$ is a prime number or a natural power of two. -/
theorem number_theory_24349 {a : ℕ → ℕ} {n k d a0 : ℕ} (hn : n > 6)
    (ha : ∀ i, a i = a0 + i * d) (dnz : d ≠ 0)
    (h: {m : ℕ | m < n ∧ n.Coprime m} = {a i | i ≤ k}) :
    Nat.Prime n ∨ (∃ i, n = 2 ^ i) := by
  -- the first term is 1, since 1 and n are coprime
  have set_mem_1: 1 ∈ {m | m < n ∧ n.Coprime m} := by
    simp only [Set.mem_setOf_eq,
    Nat.coprime_one_right_eq_true, and_true]
    linarith only [hn]
  have ha0: a0 = 1 := by
    have h2: ∀ m ∈ {m | m < n ∧ n.Coprime m}, 1 ≤ m := by
      intro m
      simp only [Set.mem_setOf_eq, and_imp]
      intro mlt mco
      by_contra!
      replace: m = 0 := Nat.lt_one_iff.mp this
      simp only [this, Nat.coprime_zero_right] at mco
      simp [mco] at hn
    simp only [h, Set.mem_setOf_eq, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂] at h2
    specialize h2 0 (by simp)
    simp only [ha, zero_mul, add_zero] at h2
    simp only [h, Set.mem_setOf_eq] at set_mem_1
    rcases set_mem_1 with ⟨i0, hi0⟩
    have h1: i0 = 0 := by
      rw [← hi0.right, ha i0] at h2
      simp only [add_le_iff_nonpos_right, nonpos_iff_eq_zero,
      mul_eq_zero, dnz, or_false] at h2
      exact h2
    simp only [h1, zero_le, ha, zero_mul, add_zero, true_and] at hi0
    exact hi0
  simp only [ha, ha0] at h

  -- n-1 is largest number < n and coprime to n, so value of k is determined.
  have set_mem_n_sub_one: n-1 ∈ {m | m < n ∧ n.Coprime m} := by
    simp only [Set.mem_setOf_eq, tsub_lt_self_iff,
    Nat.lt_one_iff, pos_of_gt, and_true]
    refine ⟨(by omega), ?_⟩
    refine (Nat.coprime_self_sub_right (by omega)).mpr ?_
    exact Nat.gcd_one_right n

  have hk: k*d = n - 2 := by
    rw [h] at set_mem_n_sub_one
    simp only [Set.mem_setOf_eq] at set_mem_n_sub_one
    rcases set_mem_n_sub_one with ⟨k0, hk0⟩
    have k0eq: k0 = k := by
      by_contra!
      replace: k0+1 ≤ k := by
        change k0 < k
        apply lt_of_le_of_ne hk0.left this
      replace: 1 + (k0+1) * d ∈ {x | ∃ i ≤ k, 1 + i*d = x} := by
        simp only [Set.mem_setOf_eq]
        use (k0+1),this
      rw [← h] at this
      simp only [Set.mem_setOf_eq] at this
      rw [add_one_mul, ← add_assoc, hk0.right] at this
      have: d = 0 := by omega
      simp [this] at dnz
    rw [k0eq] at hk0
    omega

  -- the set contain at least two elements given n > 1.
  -- so k ≠ 0.
  have kpos: 0 < k := by
    by_contra!
    replace: k = 0 := by omega
    simp only [this, nonpos_iff_eq_zero, exists_eq_left,
    zero_mul, add_zero, Set.setOf_eq_eq_singleton'] at h
    have: n - 1 ∈ ({1}: Set ℕ) := by
      rw [← h]
      simp only [Set.mem_setOf_eq, tsub_lt_self_iff,
      Nat.lt_one_iff, pos_of_gt, and_true]
      refine ⟨(by omega), ?_⟩
      refine (Nat.coprime_self_sub_right (by omega)).mpr ?_
      exact Nat.gcd_one_right n
    simp only [Set.mem_singleton_iff,
    Nat.pred_eq_succ_iff, zero_add] at this
    simp [this] at hn

  -- if d = 1, the next term is 2. and 1,2,3,..,n-1 all coprime to n.
  -- n is prime
  by_cases hd1: d = 1
  · left
    apply Nat.prime_of_coprime n (by linarith only [hn]) ?_
    intro m hm1 hm2
    simp only [hd1, mul_one] at h hk
    have: m ∈ {x | ∃ i ≤ k, 1 + i = x} := by
      simp only [Set.mem_setOf_eq]
      use m-1; constructor
      · rw [hk]
        omega
      · omega
    rw [← h] at this
    simp only [Set.mem_setOf_eq] at this
    exact this.right


  -- if d = 2, next term is 3, n has no odd divisor.
  -- therefore n is 2-power.
  by_cases hd2: d = 2
  · by_cases pn: Nat.Prime n
    · left; exact pn
    right
    have dvd_2: 2 ∣ n := by
      by_contra!
      rw [← Nat.Prime.coprime_iff_not_dvd (by norm_num)] at this
      replace: 2 ∈ {m | m < n ∧ n.Coprime m} := by
        simp only [Set.mem_setOf_eq]
        exact ⟨(by omega), this.symm⟩
      rw [h] at this
      simp only [hd2, Set.mem_setOf_eq] at this
      -- cannot be the case 1 + 2i = 2,  contradiction.
      omega
    have: IsPrimePow n := by
      rw [isPrimePow_iff_unique_prime_dvd]
      refine existsUnique_of_exists_of_unique ?_ ?_
      · refine ⟨2, (by norm_num), dvd_2⟩
      · have: ∀p, Nat.Prime p → p ∣ n → p = 2 := by
          intro p pp pdvd
          by_cases hp: p = 2
          · exact hp
          · replace hp := pp.odd_of_ne_two hp
            have plt: p < n := by
              apply lt_of_le_of_ne ?_ ?_
              · apply Nat.le_of_dvd (by omega) pdvd
              · by_contra!
                rw [this] at pp
                exact pn pp
            change p+1 ≤ n at plt
            have: p ∈ {x | ∃ i ≤ k, 1 + i*d = x} := by
              simp only [hd2, Set.mem_setOf_eq]
              rcases (odd_iff_exists_bit1.mp hp) with ⟨j, hj⟩
              use j
              simp only [hj, mul_comm, add_comm, and_true]
              suffices 2*j+1 ≤ 2*k+1 by
                simp only [add_le_add_iff_right,
                Nat.ofNat_pos, mul_le_mul_left] at this
                exact this
              have: 2*k+1 = n - 1 := by
                rw [hd2] at hk
                omega
              rw [this, ← hj]
              exact Nat.le_sub_one_of_lt plt
            rw [← h] at this
            simp only [Set.mem_setOf_eq] at this
            absurd pdvd
            rw [← pp.coprime_iff_not_dvd]
            exact this.right.symm
        intro p1 p2 hp1 hp2
        have h1 := this p1 hp1.left hp1.right
        have h2 := this p2 hp2.left hp2.right
        simp only [h1, h2]
    rw [isPrimePow_nat_iff] at this
    rcases this with ⟨p, i, pp, ipos, neq⟩
    have peq: p = 2 := by
      rw [← neq] at dvd_2
      have p2: Nat.Prime 2 := by norm_num
      replace dvd_2: 2 ∣ p := p2.dvd_of_dvd_pow dvd_2
      rwa [pp.dvd_iff_eq (by norm_num)] at dvd_2
    use i
    rw [← neq, peq]

  -- d > 2 case.
  -- consider prime factor of d.
  -- it must divide n, otherwise it's i d + 1 for some i, impossible.
  have d_dvd: ∀p:ℕ, Nat.Prime p → p ∣ d → p ∣ n := by
    intro p pp pdvd
    have ple: p ≤ d := Nat.le_of_dvd (by omega) pdvd
    by_contra!
    rw [← pp.coprime_iff_not_dvd] at this
    replace: p ∈ {m | m < n ∧ n.Coprime m} := by
      simp only [Set.mem_setOf_eq]
      refine ⟨?_, this.symm⟩
      have h2: d < n := by
        suffices d ≤ n-2 by omega
        rw [← hk]
        exact Nat.le_mul_of_pos_left d kpos
      exact lt_of_le_of_lt ple h2
    rw [h] at this
    simp only [Set.mem_setOf_eq] at this
    rcases this with ⟨i0, hi0⟩
    absurd ple
    push_neg
    rw [← hi0.right]
    suffices i0 ≠ 0 by
      replace: i0 ≥ 1 := by omega
      rw [add_comm 1 _]
      suffices d ≤ i0*d by
        exact Order.lt_add_one_iff.mpr this
      exact Nat.le_mul_of_pos_left d this
    rintro rfl
    simp only [zero_le, zero_mul, add_zero, true_and] at hi0
    norm_num [← hi0] at pp

  -- but it also divide n-2, therefore it divide 2, and just equal 2.
  replace d_dvd: ∀p:ℕ, Nat.Prime p → p ∣ d → p = 2 := by
    intro p pp pdvd
    have h1 := d_dvd p pp pdvd
    have h2: p ∣ n - 2 := by
      rw [← hk]
      exact pdvd.mul_left k
    suffices p ∣ 2 by
      rw [Nat.Prime.dvd_iff_eq (by norm_num) pp.ne_one] at this
      exact this.symm
    have: 2 = n - (n-2) := by omega
    rw [this]
    exact Nat.dvd_sub' h1 h2

  -- then d is a 2-power.
  obtain ⟨i0, hi0⟩: ∃ i0, d = 2^i0 := by
    have h1: IsPrimePow d := by
      rw [isPrimePow_iff_unique_prime_dvd]
      use 2
      simp only [and_imp]
      constructor
      · refine ⟨(by norm_num), ?_⟩
        suffices d.minFac = 2 by
          rw [← this]
          exact Nat.minFac_dvd d
        apply d_dvd _ ?_ ?_
        · exact Nat.minFac_prime hd1
        · exact Nat.minFac_dvd d
      · exact d_dvd
    rw [isPrimePow_nat_iff] at h1
    rcases h1 with ⟨p, i, pp, ipos, hd⟩
    use i
    rw [← hd]
    suffices p = 2 by
      rw [this]
    apply d_dvd p pp ?_
    rw [← hd]
    exact dvd_pow_self p ipos.ne'

  -- 3 is not 1 + i d, given d > 2.
  have not_mem_3: 3 ∉ {x | ∃ i ≤ k, 1 + i * d = x} := by
    simp only [Set.mem_setOf_eq, not_exists, not_and]
    intro i hi
    by_contra!
    have h1: i < 1 := by
      suffices 1 + i * d < 1 + d by
        simp only [add_lt_add_iff_left] at this
        exact lt_one_of_mul_lt_left this
      rw [this]
      omega
    have h2: i ≠ 0 := by
      rintro rfl
      simp at this
    omega

  -- since d ≠ 2, 3 divide n.
  have dvd_3: 3 ∣ n := by
    by_contra!
    rw [← Nat.Prime.coprime_iff_not_dvd (by norm_num)] at this
    have: 3 ∈ {m | m < n ∧ n.Coprime m} := by
      simp only [Set.mem_setOf_eq]
      exact ⟨(by omega), this.symm⟩
    rw [h] at this
    apply not_mem_3 this

  -- then 3 not divide m, if m coprime to n
  have not_3_dvd_of_co {m: ℕ} (co: n.Coprime m):
    ¬ 3 ∣ m := by
    rintro hdvd
    have: 3 ∣ 1 := by
      rw [← co]
      apply Nat.dvd_gcd dvd_3 hdvd
    norm_num at this

  -- k ≥ 2, otherwise only two numbers coprime to n.
  have kge: k ≥ 2 := by
    by_contra!
    replace: k = 1 := by omega
    replace: {x | ∃ i ≤ k, 1 + i * d = x} = {1, 1 + d} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, hi⟩
        rw [← hi.right]
        replace hi: i = 0 ∨ i = 1 := by
          rw [this] at hi
          omega
        rcases hi with (rfl | rfl)
        <;> simp
      · rintro (rfl | rfl)
        · use 0; simp [this]
        · use 1; simp [this]
    rw [h, this] at set_mem_1 set_mem_n_sub_one
    rw [this] at h
    replace h: 2 < Nat.card ↑({1,1+d}: Set ℕ) := by
      rw [← h, ← Nat.totient_eq_card_lt_and_coprime]
      exact l_two_lt_totient_of_six_lt hn
    absurd h
    push_neg
    simp only [Nat.card_eq_fintype_card, Fintype.card_ofFinset,
    Set.toFinset_singleton, Finset.card_le_two]

  -- d+1, 2d+1 both coprime to n.
  have h1: Nat.Coprime n (2^i0+1) := by
    rw [← hi0, add_comm]
    have: 1 + d ∈ {x | ∃ i≤ k, 1 + i*d = x} := by
      simp only [Set.mem_setOf_eq, add_right_inj]
      use 1
      simpa only [one_mul, and_true] using kpos
    rw [← h] at this
    simp only [Set.mem_setOf_eq] at this
    exact this.right
  have h2: Nat.Coprime n (2^(i0+1) + 1) := by
    rw [pow_succ', ← hi0, add_comm _ 1]
    suffices (1 + 2*d) ∈ {m | m < n ∧ n.Coprime m} by
      simp only [Set.mem_setOf_eq] at this
      exact this.right
    simp only [h, Set.mem_setOf_eq, add_right_inj,
    mul_eq_mul_right_iff]
    use 2,kge
    simp only [true_or]

  -- but cannot be the case 2^i+1, 2^(i+1) neither divided by 3.
  by_cases h3: Odd i0
  · specialize not_3_dvd_of_co h1
    absurd not_3_dvd_of_co
    apply l_three_dvd_two_odd_pow_add_one h3
  · specialize not_3_dvd_of_co h2
    absurd not_3_dvd_of_co
    refine l_three_dvd_two_odd_pow_add_one ?_
    exact Nat.odd_add_one.mpr h3