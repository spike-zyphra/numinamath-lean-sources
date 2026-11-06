import Mathlib

/- Let $S^{}_{}$ be the set of all rational numbers $r^{}_{}$, $0^{}_{}<r<1$, that have a repeating decimal expansion in the form $0.abcabcabc\ldots=0.\overline{abc}$, where the digits $a^{}_{}$, $b^{}_{}$, and $c^{}_{}$ are not necessarily distinct. To write the elements of $S^{}_{}$ as fractions in lowest terms, how many different numerators are required? -/
theorem number_theory_96003 :
    Set.ncard {n : ℕ | ∃ r : ℚ, 0 < r ∧ r < 1 ∧ r.num = n ∧ ∃ k : ℕ, r = k / 999} = 660 := by

  -- Equivalently, the problem is asking for the number of values k / gcd(k, 999)
  -- for k in the range 0 < k < 999.
  have : {n : ℕ | ∃ r : ℚ, 0 < r ∧ r < 1 ∧ r.num = n ∧ ∃ abc : ℕ, r = abc/999} =
      {n : ℕ | ∃ k : ℕ, 0 < k ∧ k < 999 ∧ k / Nat.gcd k 999 = n} := by
    ext n
    simp
    constructor
    . rintro ⟨r, hr1, hr2, hr3, ⟨k, hk⟩⟩
      use k
      and_intros
      . qify; linarith
      . qify; linarith
      . zify;
        rw [← hr3, hk]
        rw [show (k / 999 : ℚ) = Rat.divInt k 999 by simp [← Rat.intCast_div_eq_divInt]]
        rw [Rat.num_mk, Int.sign_eq_one_of_pos (show 0 < 999 by norm_num)]
        simp
        rfl
    . rintro ⟨k, hk1, hk2, hk3⟩
      use Rat.divInt k 999
      and_intros
      . rw [Rat.divInt_eq_div]
        simp
        linarith
      . rw [Rat.divInt_eq_div]
        simp
        qify at hk2
        linarith
      . rw [← hk3, Rat.num_mk, Int.sign_eq_one_of_pos (show 0 < 999 by norm_num)]
        simp
        rfl
      . use k
        rw [Rat.divInt_eq_div]
        simp
  rw [this]

  have factors : 999 = 3^3 * 37 := by simp

  -- We show there are only two possibilities: either n is coprime to 999 (if k is not divisible by 81)
  -- or n is divisible by 3 (if k is divisible by 81).
  have : {n : ℕ | ∃ k : ℕ, 0 < k ∧ k < 999 ∧ k / Nat.gcd k 999 = n} =
      {n ∈ Finset.Ico 1 999 | Nat.Coprime n 999} ∪ {n ∈ Finset.Ioc 0 36 | 3 ∣ n} := by
    ext n
    simp
    constructor
    -- In the forward direction, we split into two cases, if 81 ∣ k or not.
    . rintro ⟨k, hk1, hk2, hk3⟩
      by_cases h : 3^4 ∣ k
      -- If 81 ∣ k, then k cannot be divisible by 37, so gcd(k, 999) = 27 and
      -- k / gcd(k, 999) is divisible by 3.
      . apply Or.inr
        have : Nat.gcd k 999 = 27 := by
          rw [factors, Nat.Coprime.gcd_mul _ (by norm_num), Nat.gcd_eq_right (by omega)]
          have : Nat.Coprime k 37 := by
            rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (by norm_num)]
            omega
          rw [Nat.Coprime.gcd_eq_one this]
          simp
        rw [this] at hk3
        and_intros
        all_goals omega
      -- Otherwise, we can show that k is coprime to 999.
      . apply Or.inl
        have n_pos : 1 ≤ n := by
          rw [← hk3, Nat.one_le_div_iff (Nat.gcd_pos_of_pos_right _ (by norm_num))]
          exact Nat.gcd_le_left _ hk1
        and_intros
        . exact n_pos
        . rw [← hk3]
          exact lt_of_le_of_lt (Nat.div_le_self _ _) hk2
        . apply Nat.coprime_of_dvd
          intro p hp hdivn hdiv999
          -- To show that k is coprime to 999, we use the following fact:
          have {p} (hp : Nat.Prime p) : Nat.factorization n p = Nat.factorization k p - Nat.factorization 999 p := by
            rw [← hk3, Nat.factorization_div (Nat.gcd_dvd_left _ _)]
            rw [Nat.factorization_gcd (by linarith) (by norm_num)]
            simp
            rw [← Nat.sub_eq_sub_min]
          -- This implies that if p divides n, it appears in the factorization of k more times
          -- than it does in 999.
          have {p e} (hp : Nat.Prime p) (h : p ∣ n) (he : Nat.factorization 999 p = e) : p^(e + 1) ∣ k := by
            rw [Nat.Prime.pow_dvd_iff_le_factorization hp (by linarith), ← he]
            apply Nat.add_one_le_of_lt
            apply Nat.lt_of_sub_pos
            rw [← this hp]
            exact Nat.Prime.factorization_pos_of_dvd hp (by linarith) h
          rw [factors, Nat.Prime.dvd_mul hp] at hdiv999
          rcases hdiv999 with (h | h)
          . replace h := Nat.prime_eq_prime_of_dvd_pow hp (by norm_num) h
            subst h
            -- For p = 3, we have 81 ∣ k, which contradicts our assumption.
            have : 3^4 ∣ k := by
              apply this hp hdivn
              rw [factors, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.coe_add, Pi.add_apply]
              rw [Nat.factorization_pow, Nat.Prime.factorization (show Nat.Prime 3 by norm_num), Nat.Prime.factorization (show Nat.Prime 37 by norm_num)]
              simp
            contradiction
          . rw [Nat.prime_dvd_prime_iff_eq hp (by norm_num)] at h
            subst h
            -- For p = 37, we have 37^2 ∣ k, which implies k > 999.
            have : 37^2 ∣ k := by
              apply this hp hdivn
              rw [factors, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.coe_add, Pi.add_apply]
              rw [Nat.factorization_pow, Nat.Prime.factorization (show Nat.Prime 3 by norm_num), Nat.Prime.factorization (show Nat.Prime 37 by norm_num)]
              simp
            have : 999 ≤ k := by omega
            linarith
    -- In the reverse direction, if n is coprime to n, we can just use n. If n is divisible by 3,
    -- we use 27 * n.
    . rintro (⟨⟨hk1, hk2⟩, h⟩ | ⟨⟨hk1, hk2⟩, h⟩)
      . use n
        and_intros
        . linarith
        . linarith
        . simp [h]
      . use 3^3 * n
        and_intros
        . linarith
        . linarith
        . have : Nat.Coprime (3^3 * n) 37 := by
            apply Nat.Coprime.mul (by norm_num)
            rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (by norm_num)]
            exact Nat.not_dvd_of_pos_of_lt hk1 (by linarith)
          rw [factors, Nat.Coprime.gcd_mul _ (show Nat.Coprime (3^3) 37 by norm_num),
            Nat.gcd_mul_right_left, Nat.Coprime.gcd_eq_one this]
          simp
  rw [this]

  -- These two sets are disjoint so we can count them separately.
  have : Disjoint {n ∈ Finset.Ico 1 999 | Nat.Coprime n 999} {n ∈ Finset.Ioc 0 36 | 3 ∣ n} := by
    rw [Finset.disjoint_left]
    simp
    intro n _ _ hcoprime _ _ hdiv
    have : 3 ∣ 1 := by
      rw [Nat.Coprime] at hcoprime
      rw [← hcoprime, Nat.dvd_gcd_iff]
      exact ⟨hdiv, by norm_num⟩
    have : ¬(3 ∣ 1) := by norm_num
    contradiction
  rw [Set.ncard_coe_Finset, Finset.card_union_of_disjoint this]

  -- We can compute the first sum with the totient function.
  have : {n ∈ Finset.Ico 1 999 | Nat.Coprime n 999}.card = Nat.totient 999 := by
    rw [Nat.totient_eq_card_coprime, Finset.range_eq_Ico]
    nth_rw 1 [Finset.filter_congr (fun x _ => Nat.coprime_comm)]
    nth_rw 2 [← Nat.Ico_insert_succ_left (by norm_num)]
    rw [Finset.filter_insert]
    simp
  rw [this, factors, Nat.totient_mul (by norm_num),
    Nat.totient_prime_pow (by norm_num) (by norm_num), Nat.totient_prime (by norm_num)]

  -- For the second sum we can use a standard formula for the number of multiples of 3 in a range.
  simp_rw [← Nat.modEq_zero_iff_dvd]
  zify
  rw [Nat.Ioc_filter_modEq_card _ _ (by norm_num)]
  norm_cast