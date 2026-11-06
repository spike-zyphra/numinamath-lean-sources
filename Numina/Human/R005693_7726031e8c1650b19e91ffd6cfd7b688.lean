import Mathlib

set_option exponentiation.threshold 3000
set_option maxHeartbeats 1000000

lemma factorization_prod_pow_eq_self {n : ℕ} (hn: n ≠ 0):
  n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
  nth_rw 1 [← Nat.factorization_prod_pow_eq_self hn]
  rfl


lemma factor_2015 {a b c : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : a ≤ b) (hbc : b ≤ c) (habc : a * b * c = 2015) :
  a = 5 ∧ b = 13 ∧ c = 31 := by
  have h1 : a ≤ 12 := by
    by_contra h
    push_neg at h
    have : a ≥ 13 := by omega
    have : a * b ≥ 13 * 13 := by nlinarith
    nlinarith
  interval_cases a <;> try {
    have h2 : b ≤ 31 := by nlinarith
    interval_cases b <;> omega
  }

lemma dvd_prime_mul_prime {c p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : c ∣ p * q) :
    c = 1 ∨ c = p ∨ c = q ∨ c = p * q := by
  have h1 : c ∣ p * q := h
  have h4 : c ∣ p * q := h1
  rcases (Nat.dvd_mul).mp h4 with ⟨k, m, hk, hm, hc⟩
  have h5 : k ∣ p := by
    simpa using hk
  have h6 : m ∣ q := by
    simpa using hm
  have h7 : k = 1 ∨ k = p := by
    have hp2 : p.Prime := hp
    have h8 : k ∣ p := h5
    have h9 : k = 1 ∨ k = p := by
      apply (Nat.dvd_prime hp2).mp at h8
      rcases h8 with (h10 | h11)
      · left
        omega
      · right
        omega
    tauto
  have h8 : m = 1 ∨ m = q := by
    have hq2 : q.Prime := hq
    have h9 : m ∣ q := h6
    have h10 : m = 1 ∨ m = q := by
      apply (Nat.dvd_prime hq2).mp at h9
      rcases h9 with (h11 | h12)
      · left
        omega
      · right
        omega
    tauto
  rcases h7 with (hk1 | hk2)
  · -- k = 1
    rcases h8 with (hm1 | hm2)
    · -- m = 1
      have hc1 : c = 1 := by
        nlinarith [hc, hk1, hm1]
      simp [hc1]
    · -- m = q
      have hc2 : c = q := by
        nlinarith [hc, hk1, hm2]
      simp [hc2]
  · -- k = p
    rcases h8 with (hm1 | hm2)
    · -- m = 1
      have hc3 : c = p := by
        nlinarith [hc, hk2, hm1]
      simp [hc3]
    · -- m = q
      have hc4 : c = p * q := by
        nlinarith [hc, hk2, hm2]
      simp [hc4]


lemma factor_two_three {a b c p q : ℕ}
  (hp : p.Prime) (hq : q.Prime)
  (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (h : a * b * c = p * q) :
  False := by
  have : c ∣ p * q := by
    rw [← h]
    simp
  
  apply dvd_prime_mul_prime at this
  . rcases this with rfl | rfl | rfl | rfl
    . simp at hc
    . have : a * b = q := by nlinarith
      have : a ∣ q := by use b; omega
      rw [Nat.dvd_prime_two_le] at this
      subst a
      have : b = 1 := by nlinarith
      subst b
      simp at hb
      all_goals assumption
    . have : a * b = p := by nlinarith
      have : a ∣ p := by use b; omega
      rw [Nat.dvd_prime_two_le] at this
      subst a
      have : b = 1 := by nlinarith
      subst b
      simp at hb
      all_goals assumption
    . have : a * b = 1 := by nlinarith
      simp at this
      omega
  all_goals assumption

lemma factor_2015_four {a b c d : ℕ}
  (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d) (h : a * b * c * d = 2015) :
  False := by
  have h1 : d ∈ Nat.divisors (2015) := by
    rw [← h]
    simp
    omega

  have h2 : Nat.divisors 2015 = {1, 5, 13, 31, 65, 155, 403, 2015} := by native_decide

  rw [h2] at h1
  simp at h1

  rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  . simp at hd
  . have : a * b * c = 403 := by linarith
    apply @factor_two_three a b c 13 31
    all_goals try decide
    all_goals assumption
  . have : a * b * c = 155 := by linarith
    apply @factor_two_three a b c 5 31
    all_goals try decide
    all_goals assumption
  . have : a * b * c = 65 := by linarith
    apply @factor_two_three a b c 5 13
    all_goals try decide
    all_goals assumption
  . have : a * b * c = 31 := by linarith
    have : c ∣ 31 := by use a * b; rw [← this]; ring
    rw [Nat.dvd_prime_two_le] at this
    subst c
    have : a * b = 1 := by nlinarith
    simp at this
    omega
    decide
    assumption

  . have : a * b * c = 13 := by linarith
    have : c ∣ 13 := by use a * b; rw [← this]; ring
    rw [Nat.dvd_prime_two_le] at this
    subst c
    have : a * b = 1 := by nlinarith
    simp at this
    omega
    decide
    assumption
  . have : a * b * c = 5 := by linarith
    have : c ∣ 5 := by use a * b; rw [← this]; ring
    rw [Nat.dvd_prime_two_le] at this
    subst c
    have : a * b = 1 := by nlinarith
    simp at this
    omega
    decide
    assumption
  . have : a * b * c = 1 := by linarith
    simp at this
    omega


lemma factor_2015_of_card_3 {n : ℕ} (h1 : n.primeFactors.card = 3) (h2 : n.divisors.card = 2015) :
  ∃ p q r : ℕ, p ≠ q ∧ p ≠ r ∧ q ≠ r
  ∧ p.Prime ∧ q.Prime ∧ r.Prime
  ∧ n = p^4 * q^12 * r^30 := by

  have hn_ne_zero : n ≠ 0 := by
    by_contra h
    rw [h] at h2
    simp at h2

  rw [Nat.card_divisors (by assumption)] at h2
  rw [Finset.card_eq_three] at h1
  obtain ⟨p, q, r, hpq, hpr, hqr, h1⟩ := h1
  rw [h1] at h2
  rw [Finset.prod_insert (by simp; omega)] at h2
  rw [Finset.prod_pair (by assumption)] at h2

  wlog hab : (n.factorization p + 1) ≤ (n.factorization q + 1)
  . apply this hn_ne_zero q p r
    all_goals try omega
    . rw [← h2]; ring
    . rw [h1]; ext x; simp; omega
  . wlog hac : (n.factorization p + 1) ≤ (n.factorization r + 1)
    . apply this hn_ne_zero r q p
      all_goals try omega
      . rw [← h2]; ring
      . rw [h1]; ext x; simp; omega
    . wlog hbc : (n.factorization q + 1) ≤ (n.factorization r + 1)
      . apply this hn_ne_zero p r q
        all_goals try omega
        . rw [← h2]; ring
        . rw [h1]; ext x; simp; omega
      . have : p ∈ n.primeFactors := by rw [h1]; simp
        simp at this
        have := this.1

        have : q ∈ n.primeFactors := by rw [h1]; simp
        simp at this
        have := this.1

        have : r ∈ n.primeFactors := by rw [h1]; simp
        simp at this
        have := this.1

        have : 2 ≤ n.factorization p + 1 := by
          by_contra h
          have : n.factorization p = 0 := by omega
          rw [Nat.factorization_eq_zero_iff] at this
          contrapose this
          simp
          refine ⟨?_, ?_, ?_⟩
          all_goals try omega
          all_goals try assumption

        have : 2 ≤ n.factorization q + 1 := by
          by_contra h
          have : n.factorization q = 0 := by omega
          rw [Nat.factorization_eq_zero_iff] at this
          contrapose this
          simp
          refine ⟨?_, ?_, ?_⟩
          all_goals try omega

        have : 2 ≤ n.factorization r + 1 := by
          by_contra h
          have : n.factorization r = 0 := by omega
          rw [Nat.factorization_eq_zero_iff] at this
          contrapose this
          simp
          refine ⟨?_, ?_, ?_⟩
          all_goals try omega

        have := @factor_2015 (n.factorization p + 1) (n.factorization q + 1) (n.factorization r + 1) (by omega) (by omega) (by omega) (by omega) (by rw [← h2]; ring)
        simp at this
        obtain ⟨hp_eq, hq_eq, hr_eq⟩ := this

        use p, q, r
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals try omega
        all_goals try assumption

        have := factorization_prod_pow_eq_self hn_ne_zero
        rw [this]
        rw [h1]
        rw [Finset.prod_insert (by simp; omega)]
        rw [Finset.prod_pair (by assumption)]
        rw [hp_eq, hq_eq, hr_eq]
        ring

theorem number_theory_609447 {n : ℕ} (hn : IsLeast {m | m.divisors.card = 2015} n) :
  n.primeFactorsList.sum = 116 := by

  suffices n = 2^30 * 3^12 * 5^4 by
    rw [this]
    native_decide

  suffices IsLeast {m | m.divisors.card = 2015} (2^30 * 3^12 * 5^4) from IsLeast.unique hn this

  constructor
  . simp only [Set.mem_setOf]
    rw [Nat.card_divisors (by norm_num)]
    native_decide
  . simp only [lowerBounds, Set.mem_setOf]

    intro n hn

    have hn_ne_zero : n ≠ 0 := by
      by_contra h
      rw [h] at hn
      simp at hn

    have hn_card := hn
    rw [Nat.card_divisors (by assumption)] at hn
    by_cases hn1 : n.primeFactors.card = 1
    . rw [Finset.card_eq_one] at hn1
      obtain ⟨p, hp⟩ := hn1
      rw [hp] at hn
      simp at hn
      have h1 : n = p ^ 2014 := by
        have := @factorization_prod_pow_eq_self n hn_ne_zero
        rw [this]
        rw [hp]
        simp
        rw [hn]

      have h2 : 2^2014 ≤ n := by
        rw [h1]
        apply Nat.pow_le_pow_left
        have : p ∈ n.primeFactors := by
          rw [hp]
          simp
        simp at this
        have := this.1
        rw [Nat.prime_def] at this
        exact this.1

      omega
    . by_cases hn2 : n.primeFactors.card = 2
      . rw [Finset.card_eq_two] at hn2
        obtain ⟨p, q, hq, hn2⟩ := hn2
        rw [hn2] at hn
        rw [Finset.prod_pair hq] at hn
        have : (n.factorization p + 1) ∈ Nat.divisors 2015 := by
          simp
          use n.factorization q + 1
          rw [hn]

        rw [show Nat.divisors 2015 = {1, 5, 13, 31, 65, 155, 403, 2015} by native_decide] at this
        simp at this

        have hn_eq := factorization_prod_pow_eq_self hn_ne_zero
        rw [hn2] at hn_eq
        rw [Finset.prod_pair hq] at hn_eq

        have h_two_le_p : 2 ≤ p := by
          have : p ∈ n.primeFactors := by
            rw [hn2]
            simp
          simp at this
          have := this.1
          rw [Nat.prime_def] at this
          exact this.1

        have h_two_le_q : 2 ≤ q := by
          have : q ∈ n.primeFactors := by
            rw [hn2]
            simp
          simp at this
          have := this.1
          rw [Nat.prime_def] at this
          exact this.1

        rw [hn_eq]
        rcases this with h | h | h | h | h | h | h | h
        . rw [Nat.factorization_eq_zero_iff] at h
          have : p ∈ n.primeFactors := by
            rw [hn2]
            simp
          contrapose h
          simp
          simp at this
          exact this

        . rw [h, show n.factorization q = 402 by nlinarith]
          have : 2^4 ≤ p^4 := by apply Nat.pow_le_pow_left; assumption
          have : 2^402 ≤ q^402 := by apply Nat.pow_le_pow_left; assumption
          nlinarith

        . rw [h, show n.factorization q = 154 by nlinarith]
          have : 2^12 ≤ p^12 := by apply Nat.pow_le_pow_left; assumption
          have : 2^154 ≤ q^154 := by apply Nat.pow_le_pow_left; assumption
          nlinarith

        . rw [h, show n.factorization q = 64 by nlinarith]
          have : 2^30 ≤ p^30 := by apply Nat.pow_le_pow_left; assumption
          have : 2^64 ≤ q^64 := by apply Nat.pow_le_pow_left; assumption
          nlinarith

        . rw [h, show n.factorization q = 30 by nlinarith]
          have : 2^64 ≤ p^64 := by apply Nat.pow_le_pow_left; assumption
          have : 2^30 ≤ q^30 := by apply Nat.pow_le_pow_left; assumption
          nlinarith

        . rw [h, show n.factorization q = 12 by nlinarith]
          have : 2^154 ≤ p^154 := by apply Nat.pow_le_pow_left; assumption
          have : 2^12 ≤ q^12 := by apply Nat.pow_le_pow_left; assumption
          nlinarith

        . rw [h, show n.factorization q = 4 by nlinarith]
          have : 2^402 ≤ p^402 := by apply Nat.pow_le_pow_left; assumption
          have : 2^4 ≤ q^4 := by apply Nat.pow_le_pow_left; assumption
          nlinarith

        . have : n.factorization q = 0 := by nlinarith
          rw [Nat.factorization_eq_zero_iff] at this
          contrapose this
          have : q ∈ n.primeFactors := by
            rw [hn2]
            simp
          simp at this
          simp
          exact this


      . have hn3 : n.primeFactors.card = 3 := by
          by_contra
          have : n.primeFactors.card ≠ 0 := by
            by_contra h
            simp at h
            have : n = 1 := by omega
            subst n
            simp at hn

          have : 4 ≤ n.primeFactors.card := by omega

          have : 2 < n.primeFactors.card := by omega
          rw [Finset.two_lt_card] at this
          obtain ⟨a, ha, b, hb, c, hc, hab, hbc, hac⟩ := this
          have := Finset.prod_erase_mul n.primeFactors (fun x => (n.factorization x + 1)) ha
          simp at this
          rw [← this] at hn

          have hb2 : b ∈ n.primeFactors.erase a := by
            simp
            simp at hb
            exact ⟨Ne.symm hab, hb⟩

          have := Finset.prod_erase_mul (n.primeFactors.erase a) (fun x => (n.factorization x + 1)) hb2
          simp at this
          rw [← this] at hn

          have hc2 : c ∈ (n.primeFactors.erase a).erase b := by
            simp
            simp at hc
            exact ⟨Ne.symm hac, Ne.symm hbc, hc⟩

          have := Finset.prod_erase_mul ((n.primeFactors.erase a).erase b) (fun x => (n.factorization x + 1)) hc2
          simp at this
          rw [← this] at hn

          let d := (∏ x ∈ ((n.primeFactors.erase a).erase b).erase c, (n.factorization x + 1))
          have h_two_le_d : 2 ≤ d := by
            have : ∏ x ∈ ((n.primeFactors.erase a).erase b).erase c, (1 + 1) ≤ d := by
              apply Finset.prod_le_prod
              . intro i hi
                simp
              . intro i hi
                by_contra h
                simp at h
                rw [Nat.factorization_eq_zero_iff] at h
                simp at hi
                obtain ⟨hi1, hi2, hi3, hi4⟩ := hi
                contrapose h
                simp 
                exact hi4

            simp at this
            suffices 1 ≤ (((n.primeFactors.erase a).erase b).erase c).card by
              have : 2 ^ 1 ≤ 2 ^ (((n.primeFactors.erase a).erase b).erase c).card := by
                apply Nat.pow_le_pow_right <;> omega
              linarith

            have : n.primeFactors.card - 1 ≤ (n.primeFactors.erase a).card := Finset.pred_card_le_card_erase
            have : (n.primeFactors.erase a).card - 1 ≤ ((n.primeFactors.erase a).erase b).card := Finset.pred_card_le_card_erase
            have : ((n.primeFactors.erase a).erase b).card - 1 ≤ (((n.primeFactors.erase a).erase b).erase c).card := Finset.pred_card_le_card_erase

            omega

          have h_two_le_a : 2 ≤ n.factorization a + 1 := by
            by_contra
            have : n.factorization a = 0 := by omega
            rw [Nat.factorization_eq_zero_iff] at this
            contrapose this
            simp
            simp at ha
            exact ha 
          have h_two_le_b : 2 ≤ n.factorization b + 1 := by
            by_contra
            have : n.factorization b = 0 := by omega
            rw [Nat.factorization_eq_zero_iff] at this
            contrapose this
            simp
            simp at hb
            exact hb 
          have h_two_le_c : 2 ≤ n.factorization c + 1 := by
            by_contra
            have : n.factorization c = 0 := by omega
            rw [Nat.factorization_eq_zero_iff] at this
            contrapose this
            simp
            simp at hc
            exact hc
          
          apply @factor_2015_four d (n.factorization c + 1) (n.factorization b + 1) (n.factorization a + 1)
          all_goals assumption
          
        have ⟨p, q, r, hpq, hpr, hqr, hp, hq, hr, hn⟩ := @factor_2015_of_card_3 n hn3 hn_card

        rw [hn]
        by_contra h_contra
        push_neg at h_contra

        have h_two_le_p : 2 ≤ p := by
          rw [Nat.prime_def] at hp
          exact hp.1

        have h_two_le_q : 2 ≤ q := by
          rw [Nat.prime_def] at hq
          exact hq.1

        have h_two_le_r : 2 ≤ r := by
          rw [Nat.prime_def] at hr
          exact hr.1

        by_cases hr1 : 3 ≤ r
        . have : 2^4 ≤ p^4 := by apply Nat.pow_le_pow_left; assumption
          have : 2^12 ≤ q^12 := by apply Nat.pow_le_pow_left; assumption
          have : 3^30 ≤ r^30 := by apply Nat.pow_le_pow_left; assumption
          have : 2^4 * 2^12 ≤ p^4 * q^12 := by nlinarith
          have : 2^4 * 2^12 * 3^30 ≤ p^4 * q^12 * r^30 := by nlinarith
          omega
        . have : r = 2 := by omega
          subst r
          have : p ^ 4 * q ^ 12 < 3 ^ 12 * 5 ^ 4 := by nlinarith
          have : 3 ≤ p := by omega
          have : 3 ≤ q := by omega
          by_cases hq1 : 4 ≤ q
          . have : 4^12 ≤ q^12 := by apply Nat.pow_le_pow_left; assumption
            have : 3^4 ≤ p^4 := by apply Nat.pow_le_pow_left; assumption
            have : 3^4 * 4^12 < 3^4 * 3^12 := by nlinarith
            omega
          . have : q = 3 := by omega
            subst q
            have : 5 ≤ p := by
              by_contra h
              interval_cases p
              . norm_num at hpq
              . contrapose hp
                decide

            have : 5 ^ 4 ≤ p ^ 4 := by apply Nat.pow_le_pow_left; assumption
            omega
