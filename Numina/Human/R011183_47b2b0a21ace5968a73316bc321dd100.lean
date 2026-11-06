import Mathlib

/- by Fermat little theorem, a^(p-1) ≡ 1 (mod p). therefore p ∣ a^(p-1) - 1 -/
lemma Int.natCast_dvd_pow_card_sub_one_sub_one {p a: ℕ} (pp: Nat.Prime p) (co: a.Coprime p):
  (p:ℤ) ∣ a^(p-1) - 1 := by
  have: a^(p-1) ≡ 1 [ZMOD p] := by
    refine Int.ModEq.pow_card_sub_one_eq_one pp ?_
    exact Nat.isCoprime_iff_coprime.mpr co
  symm at this
  rwa [Int.modEq_iff_dvd] at this

/- by Fermat little theorem, p ∣ a^(p-1) - 1, then p also divide a^p - a -/
lemma Int.natCast_dvd_pow_card_sub_self {p a: ℕ} (pp: Nat.Prime p) (co: a.Coprime p):
  (p:ℤ) ∣ a^p - a := by
  have h1: a^p - (a:ℤ) = a * (a^(p-1) - 1) := by
    have: p = p-1+1 := by simp [pp.one_le]
    nth_rw 1 [this, pow_succ]
    ring
  have h2 := Int.natCast_dvd_pow_card_sub_one_sub_one pp co
  rw [h1]
  apply h2.trans ?_
  apply Int.dvd_mul_left


/- II. (50 points) Find all prime pairs $(p, q)$ such that $p q \mid 5^{p}+5^{q}$. -/
theorem number_theory_229487 {p q: ℕ}
  (pp: Nat.Prime p) (pq: Nat.Prime q):
  p*q ∣ 5^p + 5^q ↔
  (  (p=2 ∧ q=3) ∨ (p=3 ∧ q=2) ∨ (p=2 ∧ q=5) ∨ (p=5 ∧ q=2) ∨
    (p=5 ∧ q=5) ∨ (p=5 ∧ q=313) ∨ (p=313 ∧ q=5)  ) := by

  -- if p,q ≠ 2,5, the divide relation cannot hold.
  have case_not_2_5 (p q: ℕ) (pp: Nat.Prime p) (pq: Nat.Prime q)
    (pne2: p ≠ 2) (pne5: p ≠ 5)
    (qne2: q ≠ 2) (qne5: q ≠ 5):
    ¬ p*q ∣ 5^p + 5^q := by
    rintro hdvd
    -- right side extract factor 5.
    replace hdvd: p*q ∣ 5^(p-1) + 5^(q-1) := by
      have: 5^p + 5^q = 5 * (5^(p-1) + 5^(q-1)) := by
        have h1: p = p-1+1 := by simp [pp.one_le]
        have h2: q = q-1+1 := by simp [pq.one_le]
        nth_rw 1 [h1, h2, pow_succ, pow_succ]
        ring
      rw [this] at hdvd
      have co: Nat.Coprime (p*q) 5 := by
        have p5: Nat.Prime 5 := by norm_num
        refine Nat.Coprime.mul ?_ ?_
        <;> simp [Nat.coprime_primes, p5, pp, pq, pne5, qne5]
      apply co.dvd_mul_left.mp hdvd
    have: p-1 ≠ 0 := Nat.sub_ne_zero_of_lt pp.one_lt
    rcases (Nat.exists_eq_two_pow_mul_odd this)
      with ⟨k1, m1, oddm1, hkm1⟩
    replace: q - 1 ≠ 0 := Nat.sub_ne_zero_of_lt pq.one_lt
    rcases (Nat.exists_eq_two_pow_mul_odd this)
      with ⟨k2, m2, oddm2, hkm2⟩
    -- if we suppose p ≠ 2, then 1,-1 mod p are distinct.
    have not_h2 {r: ℕ} (pr: Nat.Prime r) (rne: r ≠ 2):
      ¬ 1 ≡ -1 [ZMOD r] := by
      rintro h2
      replace h2: 2 ≡ 0 [ZMOD r] := by
        have hh1: (2:ℤ) = 1 + 1 := by simp
        have hh2: (0:ℤ) = -1 + 1 := by simp
        rw [hh1, hh2]
        apply h2.add rfl
      replace h2: 2 ≡ 0 [MOD r] := by
        rw [← Int.natCast_modEq_iff]
        simp [h2]
      replace h2: 2 % r = 0 := by
        apply Nat.mod_eq_of_modEq h2 pr.pos
      have: 2 < r := lt_of_le_of_ne pr.two_le rne.symm
      norm_num [Nat.mod_eq_of_lt this] at h2
    -- either k1 ≥ k2 or k2 ≤ k1, we can find contradiction.
    by_cases hk: k1 ≤ k2
    · have hmod: 5^(p-1) + 5^(q-1) ≡ 0 [ZMOD p] := by
        rw [Int.modEq_zero_iff_dvd]
        zify at hdvd
        apply Dvd.dvd.trans ?_ hdvd
        apply Int.dvd_mul_right
      -- Fermat little theorem, 5^(p-1) mod p is 1.
      have h1: 5^(p-1) ≡ 1 [ZMOD p] := by
        refine Int.ModEq.pow_card_sub_one_eq_one pp ?_
        have: (5:ℤ) = ↑(5:ℕ) := by simp
        rw [this]; symm
        refine Nat.Coprime.isCoprime ?_
        rwa [Nat.coprime_primes pp (by norm_num)]
      -- therefore 5^(q-1) mod p is -1.
      have h2: 5^(q-1) ≡ -1 [ZMOD p] := by
        have: (0:ℤ) = 5^(p-1) + - (5^(p-1)) := by simp
        rw [this] at hmod
        replace hmod: 5^(q-1) ≡ - (5^(p-1)) [ZMOD p] := by
          exact hmod.add_left_cancel' (5 ^ (p - 1))
        replace h1: - (5^(p-1)) ≡ -1 [ZMOD p] :=
          Int.neg_modEq_neg.mpr h1
        exact hmod.trans h1
      rw [hkm1] at h1
      rw [hkm2] at h2
      have h3: ((5:ℤ)^(2^k1 * m1))^(2^(k2-k1) * m2) =
        (5^(2^k2 * m2))^m1 := by
        simp only [← pow_mul]
        congr 1
        have: k2 = (k2-k1) + k1 := by simp [hk]
        nth_rw 2 [this]
        rw [pow_add]
        ring
      replace h1 := h1.pow (2^(k2-k1) * m2)
      rw [h3, one_pow] at h1
      replace h2 := h2.pow m1
      rw [oddm1.neg_one_pow] at h2
      replace h2 := h1.symm.trans h2
      apply not_h2 pp pne2 h2
    · push_neg at hk
      replace hk := hk.le
      -- basically same, this time we take modulo q.
      have hmod: 5^(q-1) + 5^(p-1) ≡ 0 [ZMOD q] := by
        rw [Int.modEq_zero_iff_dvd, add_comm]
        zify at hdvd
        apply Dvd.dvd.trans ?_ hdvd
        apply Int.dvd_mul_left
      have h1: 5^(q-1) ≡ 1 [ZMOD q] := by
        refine Int.ModEq.pow_card_sub_one_eq_one pq ?_
        have: (5:ℤ) = ↑(5:ℕ) := by simp
        rw [this]; symm
        refine Nat.Coprime.isCoprime ?_
        rwa [Nat.coprime_primes pq (by norm_num)]
      have h2: 5^(p-1) ≡ -1 [ZMOD q] := by
        have: (0:ℤ) = 5^(q-1) + - (5^(q-1)) := by simp
        rw [this] at hmod
        replace hmod: 5^(p-1) ≡ - (5^(q-1)) [ZMOD q] := by
          apply hmod.add_left_cancel' _
        replace h1: - (5^(q-1)) ≡ -1 [ZMOD q] :=
          Int.neg_modEq_neg.mpr h1
        exact hmod.trans h1
      rw [hkm2] at h1
      rw [hkm1] at h2
      have h3: ((5:ℤ)^(2^k2 * m2))^(2^(k1-k2) * m1) =
        (5^(2^k1 * m1))^m2 := by
        simp only [← pow_mul]
        congr 1
        have: k1 = (k1-k2) + k2 := by simp [hk]
        nth_rw 2 [this]
        rw [pow_add]
        ring
      replace h1 := h1.pow (2^(k1-k2) * m1)
      rw [h3, one_pow] at h1
      replace h2 := h2.pow m2
      rw [oddm2.neg_one_pow] at h2
      replace h2 := h1.symm.trans h2
      apply not_h2 pq qne2 h2

  -- if one of p,q is 5, the other is 2,5,313
  have case_p5 (p q: ℕ) (pq: Nat.Prime q)
    (peq: p = 5) (hdvd: p*q ∣ 5^p + 5^q):
    q = 2 ∨ q = 5 ∨ q = 313 := by
    by_cases hq: q = 5
    · simp [hq]
    have h1: q ∣ 5^4 + 5^(q-1) := by
      rw [peq] at hdvd
      have: 5^5 + 5^q = 5 * (5^4 + 5^(q-1)) := by
        have h1: 5 = 4+1 := by norm_num
        have h2: q = q-1+1 := by simp [pq.one_le]
        nth_rw 2 [h1]
        nth_rw 1 [h2, pow_succ, pow_succ _ (q-1)]
        ring
      rw [this] at hdvd
      apply Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
    -- Fermat little theorem, q ∣ 5^(q-1) - 1
    have h2: (q:ℤ) ∣ 5^(q-1) - 1 := by
      refine Int.natCast_dvd_pow_card_sub_one_sub_one pq ?_
      apply Nat.Coprime.symm
      rwa [Nat.coprime_primes pq (by norm_num)]
    have h3: q ∣ 2 * 313 := by
      zify at h1 ⊢
      have: (2*313:ℤ) = (5^4 + 5^(q-1)) - (5^(q-1) - 1) := by ring
      rw [this]
      apply h1.sub h2
    rw [pq.dvd_mul] at h3
    have p2: Nat.Prime 2 := by norm_num
    have p313: Nat.Prime 313 := by norm_num
    simp only [ne_eq, pq.ne_one, not_false_eq_true,
    p2.dvd_iff_eq, p313.dvd_iff_eq] at h3
    clear * - h3
    tauto

  -- if one of p,q is 2, the other is 2,3,5.
  have case_p2 (p q: ℕ) (pq: Nat.Prime q)
    (peq: p = 2) (hdvd: p*q ∣ 5^p + 5^q):
    q = 2 ∨ q = 3 ∨ q = 5 := by
    by_cases qeq: q = 5
    · simp [qeq]
    have h1: q ∣ 5^2 + 5^q := by
      rw [peq] at hdvd
      apply Dvd.dvd.trans (Nat.dvd_mul_left q 2) hdvd
    have h2: (q:ℤ) ∣ 5^q - 5 := by
      refine Int.natCast_dvd_pow_card_sub_self pq ?_
      apply Nat.Coprime.symm
      rwa [Nat.coprime_primes pq (by norm_num)]
    have h3: q ∣ 30 := by
      zify at h1 ⊢
      have: (30:ℤ) = (5^2+5^q) - (5^q-5) := by ring
      rw [this]
      apply h1.sub h2
    have: 30 = 2*3*5 := by norm_num
    rw [this] at h3
    simp only [pq.dvd_mul] at h3
    have p2: Nat.Prime 2 := by norm_num
    have p3: Nat.Prime 3 := by norm_num
    have p5: Nat.Prime 5 := by norm_num
    simp only [ne_eq, pq.ne_one, not_false_eq_true,
    p2.dvd_iff_eq, p3.dvd_iff_eq, p5.dvd_iff_eq] at h3
    clear * - h3
    tauto


  -- put them together
  constructor
  · intro hdvd
    by_cases hp2: p = 2
    · specialize case_p2 p q pq hp2 hdvd
      -- easy to check p=q=2 does not satisfy
      have qne2: q ≠ 2 := by
        rintro rfl
        norm_num [hp2] at hdvd
      simp only [hp2, true_and, Nat.reduceEqDiff, false_and, or_self, or_false, false_or]
      tauto
    · by_cases hq2: q = 2
      · rw [mul_comm, add_comm] at hdvd
        specialize case_p2 q p pp hq2 hdvd
        simp only [hp2, false_or] at case_p2
        simp [hq2, case_p2]
      · by_cases hp5: p = 5
        · specialize case_p5 p q pq hp5 hdvd
          simp [hp5, case_p5]
        · by_cases hq5: q = 5
          · rw [mul_comm, add_comm] at hdvd
            specialize case_p5 q p pp hq5 hdvd
            simp [hq5, case_p5]
          · specialize case_not_2_5 p q pp pq
              hp2 hp5 hq2 hq5 hdvd
            simp at case_not_2_5
  · -- for large exponent (when p = 313, 5^p becomes very large)
    -- we may use Fermat little theorem.
    have: 1 ≤ 5^(313-1) := by
      apply Nat.one_le_pow _ _ (by norm_num)
    have h1: 313 ∣ 5^(313-1) - 1 := by
      zify
      rw [Nat.cast_sub this, Nat.cast_pow]
      simp only [Nat.cast_ofNat, Nat.cast_one]
      apply Int.natCast_dvd_pow_card_sub_one_sub_one
      <;> norm_num
    have h2: 313 ∣ 2*313 := by apply Nat.dvd_mul_left
    have h3 := h1.add h2
    have: 5^(313-1) - 1 + 2*313 = 5^(313-1) + 5^4 := by
      zify
      rw [Nat.cast_sub this]
      simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
      rw [sub_add]
      have: 5^(313-1) + 5^4 = 5^(313-1) - (- 5^4) := by
        rw [sub_neg_eq_add]
      rw [this]
      congr 1
    rw [this] at h3
    replace: 5^313 + 5^5 = 5 * (5^(313-1) + 5^4) := by
      have hh1: 313 = 313-1+1 := by simp
      have hh2: 5 = 5-1+1 := by norm_num
      nth_rw 3 [hh2]
      nth_rw 1 [hh1, pow_succ, pow_succ]
      ring
    replace h3: 313 ∣ 5^313 + 5^5 := by
      rw [this]
      apply h3.mul_left
    have h4: 5 ∣ 5^313 + 5^5 := by
      rw [this]
      apply Nat.dvd_mul_right
    have h5: 5*313 ∣ 5^313 + 5^5 := by
      have: Nat.Coprime 5 313 := by norm_num
      apply this.mul_dvd_of_dvd_of_dvd h4 h3
    have case_pq (hpq: p = 5 ∧ q = 313):
      p*q ∣ 5^p+5^q := by
      rw [hpq.left, hpq.right, add_comm]
      exact h5
    have case_pq' (hpq: p = 313 ∧ q = 5):
      p*q ∣ 5^p + 5^q := by
      rw [hpq.left, hpq.right, mul_comm 313 5]
      exact h5
    rintro (hpq | hpq | hpq | hpq | hpq | hpq | hpq)
    all_goals try exact case_pq hpq
    all_goals try exact case_pq' hpq
    all_goals 
      rw [hpq.left, hpq.right]
      norm_num