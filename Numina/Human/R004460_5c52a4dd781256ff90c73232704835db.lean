import Mathlib

set_option maxHeartbeats 1000000

lemma factorization_prod_pow_eq_self {n : ℕ} (hn: n ≠ 0):
  n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
  nth_rw 1 [← Nat.factorization_prod_pow_eq_self hn]
  rfl

lemma divisors_of_p1_mul_p2_sq {n p1 p2 : ℕ}: n ≠ 0 ∧ n = p1 * p2 ^ 2 ∧ p1 ≠ p2 ∧ p1.Prime ∧ p2.Prime → n.divisors = {1, p2, p2 ^ 2, p1, p1 * p2, p1 * p2 ^ 2} := by
  intro ⟨hn_ne_zero, h_p1_p2_form_n, h_p1ne2, h_p1_prime, h_p2_prime⟩
  unfold Nat.divisors
  ext d
  simp
  constructor
  . rintro ⟨⟨h1, h2⟩, h3⟩
    rw [h_p1_p2_form_n] at h3
    rw [dvd_mul] at h3
    obtain ⟨d1, d2, hd1, hd2, hd12⟩ := h3
    rw [Nat.dvd_prime h_p1_prime] at hd1

    replace hd2 : (d2 = 1 ∨ d2 = p2 ∨ d2 = p2 ^ 2) := by
      rw [Nat.dvd_prime_pow h_p2_prime] at hd2
      obtain ⟨k, hk1, hk2⟩ := hd2
      interval_cases k
      . left; norm_num at hk2; exact hk2
      . right; left; norm_num at hk2; exact hk2
      . right; right; exact hk2

    rcases hd1 with rfl | rfl
    all_goals
    . rcases hd2 with rfl | rfl | rfl
      all_goals
      . norm_num at hd12
        rw [hd12]
        simp

  . rintro (h | h | h | h | h | h)
    . rw [h]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      . norm_num
      . omega
      . omega
    . have hdn1 : d ∣ n := by use p1 * p2; rw [h_p1_p2_form_n, h]; ring_nf
      have hdn2 : d ∈ n.divisors := by simp; exact ⟨hdn1, hn_ne_zero⟩
      have := Nat.pos_of_mem_divisors hdn2
      have := Nat.divisor_le hdn2
      exact ⟨by omega, hdn1⟩
    . have hdn1 : d ∣ n := by use p1; rw [h_p1_p2_form_n, h]; ring_nf
      have hdn2 : d ∈ n.divisors := by simp; exact ⟨hdn1, hn_ne_zero⟩
      have := Nat.pos_of_mem_divisors hdn2
      have := Nat.divisor_le hdn2
      exact ⟨by omega, hdn1⟩
    . have hdn1 : d ∣ n := by use p2^2; rw [h_p1_p2_form_n, h]
      have hdn2 : d ∈ n.divisors := by simp; exact ⟨hdn1, hn_ne_zero⟩
      have := Nat.pos_of_mem_divisors hdn2
      have := Nat.divisor_le hdn2
      exact ⟨by omega, hdn1⟩
    . have hdn1 : d ∣ n := by use p2; rw [h_p1_p2_form_n, h]; ring_nf
      have hdn2 : d ∈ n.divisors := by simp; exact ⟨hdn1, hn_ne_zero⟩
      have := Nat.pos_of_mem_divisors hdn2
      have := Nat.divisor_le hdn2
      exact ⟨by omega, hdn1⟩
    . have hdn1 : d ∣ n := by use 1; rw [h_p1_p2_form_n, h]; ring_nf
      have hdn2 : d ∈ n.divisors := by simp; exact ⟨hdn1, hn_ne_zero⟩
      have := Nat.pos_of_mem_divisors hdn2
      have := Nat.divisor_le hdn2
      exact ⟨by omega, hdn1⟩

theorem my_favorite_theorem :
  {n | n ∈ Finset.Icc 1000 9999
    ∧ n.divisors.card = 6
    ∧ ((n.divisors.filter (fun d => d < 10)).card = 2)
    ∧ ((n.divisors.filter (fun d => d ∈ Finset.Icc 10 99)).card = 2)
    ∧ (∃ m, m^2 ∈ n.divisors ∧
        10 ≤ m^2 ∧ m^2 ≤ 99 ∧
        ∀ d ∈ n.divisors, 10 ≤ d ∧ d ≤ 99 → d ≤ m^2)}
  = ({1127, 1421, 1519, 1813, 2009, 2107, 2303}: Set ℕ) := by


  ext n
  simp
  constructor
  . intro ⟨⟨hn1, hn2⟩, hcard, h1, h2, m, ⟨hm1, hn_ne_zero⟩, hm2, hm3, hm4⟩

    have h_factor_card_ne_1 : n.primeFactors.card ≠ 1 := by
      by_contra hf1
      rw [Nat.card_divisors hn_ne_zero] at hcard
      rw [Finset.card_eq_one] at hf1
      obtain ⟨p, hp⟩ := hf1
      rw [hp] at hcard
      simp at hcard
      have hn_eq_p_pow_5 : n = p ^ 5 := by
        rw [factorization_prod_pow_eq_self hn_ne_zero, hp]
        simp
        rw [hcard]

      have : p ∈ n.primeFactors := by rw [hp]; simp
      rw [Nat.mem_primeFactors_of_ne_zero hn_ne_zero] at this
      have ⟨h_p_prime, h_p_dvd_n⟩ := this

      rw [hn_eq_p_pow_5] at hn1

      have h_4_le_p : 4 ≤ p := by
        by_contra h2
        push_neg at h2
        have : p ^ 5 ≤ 3 ^ 5 := by
          apply Nat.pow_le_pow_left
          omega
        omega
      have h_p_le_6 : p ≤ 6 := by
        by_contra h3
        push_neg at h3
        have : 7 ^ 5 ≤ p ^ 5 := by
          apply Nat.pow_le_pow_left
          omega
        omega

      have : p = 5 := by
        interval_cases p
        . contrapose h_p_prime
          decide
        . rfl
        . contrapose h_p_prime
          decide

      subst p n
      contrapose h2
      native_decide

    have h_factor_card_le_2 : n.primeFactors.card ≤ 2 := by
      by_contra h_contra
      simp at h_contra

      suffices ∏ x ∈ n.primeFactors, (1 + 1) ≤ ∏ x ∈ n.primeFactors, (n.factorization x + 1)  by
        rw [Nat.card_divisors hn_ne_zero] at hcard
        rw [hcard] at this
        contrapose this
        simp
        have : 2 ^ 3 ≤ 2 ^ n.primeFactors.card := by
          apply Nat.pow_le_pow_right (by norm_num)
          omega
        omega

      apply Finset.prod_le_prod
      . intro i hi
        norm_num
      . intro i hi
        simp at hi
        suffices 0 < n.factorization i by omega
        apply Nat.Prime.factorization_pos_of_dvd
        . exact hi.1
        . exact hn_ne_zero
        . exact hi.2.1

    have h_factor_card_eq_2 : n.primeFactors.card = 2 := by
      by_contra h_contra
      have : n.primeFactors.card = 0 := by omega
      simp at this
      omega

    have h_p1_p2_form_n: ∃ p1 p2, n = p1 * p2 ^ 2 ∧ p1 ≠ p2 ∧ p1.Prime ∧ p2.Prime := by
      rw [Finset.card_eq_two] at h_factor_card_eq_2
      obtain ⟨p1, p2, hp1ne2, hp_set⟩ := h_factor_card_eq_2

      rw [Nat.card_divisors hn_ne_zero, hp_set, Finset.prod_pair hp1ne2] at hcard
      have : 1 ≤ n.factorization p1 := by
        have : p1 ∈ n.primeFactors := by rw [hp_set]; simp
        rw [Nat.mem_primeFactors_of_ne_zero hn_ne_zero] at this
        have ⟨h_p1_prime, h_p1_dvd_n⟩ := this
        apply Nat.Prime.factorization_pos_of_dvd
        . exact h_p1_prime
        . exact hn_ne_zero
        . exact h_p1_dvd_n

      have : n.factorization p1 ≤ 5 := by nlinarith

      have h_p1_prime : p1.Prime := by
        have : p1 ∈ n.primeFactors := by rw [hp_set]; simp
        rw [Nat.mem_primeFactors_of_ne_zero hn_ne_zero] at this
        exact this.1

      have h_p2_prime : p2.Prime := by
        have : p2 ∈ n.primeFactors := by rw [hp_set]; simp
        rw [Nat.mem_primeFactors_of_ne_zero hn_ne_zero] at this
        exact this.1

      let k := n.factorization p1
      have hk : k = n.factorization p1 := by rfl
      interval_cases n.factorization p1
      . have : n.factorization p2 = 2 := by linarith
        use p1, p2
        refine ⟨?_, hp1ne2, h_p1_prime, h_p2_prime⟩
        rw [factorization_prod_pow_eq_self hn_ne_zero]
        rw [hp_set, Finset.prod_pair hp1ne2, this]
        unfold k at hk
        rw [hk]
        ring

      . have : n.factorization p2 = 1 := by linarith
        use p2, p1
        refine ⟨?_, Ne.symm hp1ne2, h_p2_prime, h_p1_prime⟩
        . rw [factorization_prod_pow_eq_self hn_ne_zero]
          rw [hp_set, Finset.prod_pair hp1ne2, this]
          unfold k at hk
          rw [hk]
          ring
      . omega
      . omega
      . have : n.factorization p2 = 0 := by linarith
        have : p2 ∈ n.primeFactors := by rw [hp_set]; simp
        rw [Nat.mem_primeFactors_of_ne_zero hn_ne_zero] at this
        have ⟨h_p2_prime, h_p2_dvd_n⟩ := this
        suffices 0 < n.factorization p2 by omega
        apply Nat.Prime.factorization_pos_of_dvd
        . exact h_p2_prime
        . exact hn_ne_zero
        . exact h_p2_dvd_n


    obtain ⟨p1, p2, h_p1_p2_form_n, h_p1ne2, h_p1_prime, h_p2_prime⟩ := h_p1_p2_form_n

    have ⟨h_m_eq_p2, h_p2_eq_7⟩: m = p2 ∧ p2 = 7 := by
      have hn_divisors := divisors_of_p1_mul_p2_sq ⟨hn_ne_zero, h_p1_p2_form_n, h_p1ne2, h_p1_prime, h_p2_prime⟩

      have h_p2_eq_m: p2 = m := by
        have hm_ne_zero : m ≠ 0 := by
          by_contra h_contra
          rw [h_contra] at hm2
          norm_num at hm2

        have hp1_ne_zero : p1 ≠ 0 := by
          contrapose h_p1_prime
          simp at h_p1_prime
          rw [h_p1_prime]
          decide

        have hp2_ne_zero : p2 ≠ 0 := by
          contrapose h_p2_prime
          simp at h_p2_prime
          rw [h_p2_prime]
          decide

        have hp2_sq_ne_zero : p2 ^ 2 ≠ 0 := by
          contrapose h_p2_prime
          simp at h_p2_prime
          rw [h_p2_prime]
          decide

        have : m^2 ∈ n.divisors := by
          simp
          exact ⟨hm1, hn_ne_zero⟩
        rw [hn_divisors] at this
        simp at this
        rcases this with h | h | h | h | h | h
        . rw [h] at hm2; norm_num at hm2
        . have : m ∣ p2 := by use m; rw [← h]; ring
          rw [Nat.dvd_prime h_p2_prime] at this
          rcases this with rfl | rfl
          . have : p2 = 1 := by linarith
            contrapose this; omega
          . rfl
        . symm at h; exact h
        . have : m ∣ p1 := by use m; rw [← h]; ring
          rw [Nat.dvd_prime h_p1_prime] at this
          rcases this with rfl | rfl
          . have : p1 = 1 := by linarith
            contrapose this; omega
          . have : m ≤ 1 := by nlinarith
            interval_cases m <;> (contrapose h_p1_prime; omega)
        . have : (p1 * p2).factorization p1 = 1 := by
            rw [Nat.factorization_mul hp1_ne_zero hp2_ne_zero, Finsupp.add_apply]
            rw [Nat.Prime.factorization h_p1_prime]
            simp
            apply Nat.factorization_eq_zero_of_not_dvd
            by_contra h_contra
            rw [Nat.dvd_prime h_p2_prime] at h_contra
            rcases h_contra with h | h
            . rw [h] at h_p1_prime
              contrapose h_p1_prime
              decide
            . contradiction

          rw [← h, pow_two] at this
          rw [Nat.factorization_mul hm_ne_zero hm_ne_zero, Finsupp.add_apply] at this
          contrapose this
          omega

        . have : (p1 * p2 ^ 2).factorization p1 = 1 := by
            rw [Nat.factorization_mul hp1_ne_zero hp2_sq_ne_zero, Finsupp.add_apply]
            rw [Nat.Prime.factorization h_p1_prime]
            simp
            apply Nat.factorization_eq_zero_of_not_dvd
            by_contra h_contra
            rw [Nat.dvd_prime h_p2_prime] at h_contra
            rcases h_contra with h | h
            . contrapose h; omega
            . contradiction

          rw [← h, pow_two] at this
          rw [Nat.factorization_mul hm_ne_zero hm_ne_zero, Finsupp.add_apply] at this
          contrapose this
          omega


      refine ⟨h_p2_eq_m.symm, ?_⟩
      rw [← h_p2_eq_m] at hm2
      rw [← h_p2_eq_m] at hm3
      have : 4 ≤ p2 := by nlinarith
      have : p2 ≤ 10 := by nlinarith

      interval_cases p2
      . contrapose h_p2_prime
        decide
      . have : 40 ≤ p1 := by nlinarith
        by_cases hp1_le_99: p1 ≤ 99
        . have : p1 ∣ n := by
            use 25
            rw [h_p1_p2_form_n]
            ring
          have := hm4 p1 this hn_ne_zero (by omega) hp1_le_99
          rw [← h_p2_eq_m] at this
          linarith
        . simp at hp1_le_99
          suffices (Finset.filter (fun d ↦ 10 ≤ d ∧ d ≤ 99) n.divisors) = {25} by
            rw [this] at h2
            norm_num at h2

          ext d
          simp
          constructor
          . rintro ⟨⟨hd1, _⟩, hd2, hd3⟩
            have : d ∈ n.divisors := by
              simp
              exact ⟨hd1, hn_ne_zero⟩
            rw [hn_divisors] at this
            simp at this
            rcases this with h | h | h | h | h | h
            . rw [h] at hd2
              norm_num at hd2
            . rw [h] at hd2
              norm_num at hd2
            . exact h
            . rw [h] at hd3
              linarith
            . rw [h] at hd3
              linarith
            . rw [h] at hd3
              linarith

          . rintro rfl
            simp
            refine ⟨?_, hn_ne_zero⟩
            use p1
            linarith

      . contrapose h_p2_prime
        decide
      . rfl
      . contrapose h_p2_prime
        decide
      . contrapose h_p2_prime
        decide
      . contrapose h_p2_prime
        decide

    have hp1_range1 : 21 ≤ p1 := by nlinarith

    have hp1_range2 : p1 ≤ 48 := by
      by_contra h_contra
      push_neg at h_contra
      by_cases hp1_le_99 : p1 ≤ 99
      . have : p1 ∣ n := by
          use 49
          rw [h_p1_p2_form_n, h_p2_eq_7]
          ring
        have := hm4 p1 this hn_ne_zero (by omega) hp1_le_99
        rw [h_m_eq_p2, h_p2_eq_7] at this
        have : p1 = 49 := by omega
        rw [this] at h_p1_prime
        contrapose h_p1_prime
        decide

      . simp at hp1_le_99
        suffices (Finset.filter (fun d ↦ 10 ≤ d ∧ d ≤ 99) n.divisors) = {49} by
          rw [this] at h2
          simp at h2

        ext d
        simp

        constructor
        . rintro ⟨⟨hd1, _⟩, hd2, hd3⟩
          have : d ∈ n.divisors := by
            simp
            exact ⟨hd1, hn_ne_zero⟩
          rw [divisors_of_p1_mul_p2_sq ⟨hn_ne_zero, h_p1_p2_form_n, h_p1ne2, h_p1_prime, h_p2_prime⟩] at this
          rw [h_p2_eq_7] at this
          simp at this
          rcases this with h | h | h | h | h | h
          . rw [h] at hd2; norm_num at hd2
          . rw [h] at hd2; norm_num at hd2
          . exact h
          . rw [h] at hd3; omega
          . rw [h] at hd3; omega
          . rw [h] at hd3; omega

        . rintro (rfl)
          simp
          refine ⟨?_, hn_ne_zero⟩
          use p1
          rw [h_p1_p2_form_n]
          rw [h_p2_eq_7]
          ring

    subst p2
    interval_cases p1
    all_goals subst n; rw [h_p2_eq_7]; try simp
    all_goals
    . contrapose hcard
      rw [h_p2_eq_7]
      native_decide

  . rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals
    . refine ⟨?_, ?_, ?_, ?_, ?_⟩
      all_goals try native_decide
      use 7
      simp
      constructor
      . decide
      . intro d hd hd1 hd2
        by_contra h_contra
        simp at h_contra
        interval_cases d
        all_goals omega
