import Mathlib

theorem number_theory_608195 (n : ℕ) (hn : n ≠ 0) (h_factor: (∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧
  p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
  (n = p^3 ∨ n = p^2 * q ∨ n = p * q * r))): n.totient = 11^3 + 1 ↔ n ∈ ({2007, 2738, 3122}: Finset ℕ) := by

  have h1 : Nat.primeFactors 1332 = {2, 3, 37} := by
    native_decide

  have h2 : ∀ x y : ℕ, Even x → Even y → 1332 = x * y → x ∈ ({2, 6,18,74,222,666}: Finset ℕ) := by
    intro x y hx hy hxy
    have : x ∈ Nat.divisors 1332 := by
      rw [hxy]
      simp
      by_contra h
      simp at h
      by_cases hx0 : x = 0
      . subst x
        simp at hxy
      . have := h hx0
        subst y
        simp at hxy
    rw [show Nat.divisors 1332 = {1, 2, 3, 4, 6, 9, 12, 18, 36, 37, 74, 111, 148, 222, 333, 444, 666, 1332} by native_decide] at this
    simp at this
    rcases this with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals contrapose hx; try native_decide
    all_goals contrapose hy
    . have : y = 333 := by omega
      subst y
      native_decide
    . have : y = 111 := by omega
      subst y
      native_decide
    . have : y = 37 := by omega
      subst y
      native_decide
    . have : y = 9 := by omega
      subst y
      native_decide
    . have : y = 3 := by omega
      subst y
      native_decide
    . have : y = 1 := by omega
      subst y
      native_decide

  simp
  constructor
  . intro h_totient
    obtain ⟨p, q, r, hp, hq, hr, h_pq, h_pr, h_qr, h_factor⟩ := h_factor
    rcases h_factor with (h_factor | h_factor | h_factor)
    . have := Nat.totient_prime_pow hp (show 0 < 3 by omega)
      rw [← h_factor] at this
      rw [h_totient] at this
      simp at this

      have hp1: p ∈ Nat.primeFactors 1332 := by
        rw [this]
        simp
        refine ⟨?_, ?_, ?_, ?_⟩
        . exact hp
        . use p*(p-1)
          ring
        . by_contra h
          subst p
          omega
        . by_contra h
          have : p = 1 := by nlinarith
          subst p
          omega
      rw [h1] at hp1
      simp at hp1
      rcases hp1 with (rfl | rfl | rfl)
      all_goals norm_num at this

    . have : (p ^ 2).Coprime q := by
        apply Nat.Coprime.pow_left
        rw [Nat.coprime_primes]
        . exact h_pq
        . exact hp
        . exact hq
      have := @Nat.totient_mul (p^2) q this
      rw [← h_factor] at this
      rw [h_totient] at this
      rw [Nat.totient_prime_pow hp (show 0 < 2 by omega)] at this
      rw [Nat.totient_prime hq] at this
      simp at this
      have hp1: p ∈ Nat.primeFactors 1332 := by
        rw [this]
        simp
        refine ⟨?_, ?_, ?_, ?_⟩
        . exact hp
        . use (p-1)*(q-1)
          ring
        . by_contra h
          simp at h
          have : ¬ p = 0 := by
            by_contra h0
            subst p
            omega
          have := h this
          have : p = 1 := by omega
          subst p
          omega
        . by_contra h
          have : q ≤ 1 := by omega
          interval_cases q
          . omega
          . omega

      rw [h1] at hp1
      simp at hp1
      rcases hp1 with (rfl | rfl | rfl)
      . simp at this
        have : q = 667 := by omega
        subst q
        contrapose hq
        native_decide

      . simp at this
        have : q = 223 := by omega
        subst q n
        simp

      . simp at this
        have : q = 2 := by omega
        subst q n
        simp

    . have : (p * q).Coprime r := by
        unfold Nat.Coprime
        apply Nat.Coprime.mul
        . rw [Nat.coprime_primes]
          . exact h_pr
          . exact hp
          . exact hr
        . rw [Nat.coprime_primes]
          . exact h_qr
          . exact hq
          . exact hr

      have := @Nat.totient_mul (p * q) r this
      rw [← h_factor] at this
      rw [h_totient] at this
      rw [Nat.totient_mul (by
        rw [Nat.coprime_primes]
        . exact h_pq
        . exact hp
        . exact hq
      )] at this
      rw [Nat.totient_prime hp] at this
      rw [Nat.totient_prime hq] at this
      rw [Nat.totient_prime hr] at this

      by_cases h_gt_2 : (p ≠ 2) ∧ (q ≠ 2) ∧ (r ≠ 2)
      . have hp2: Even (p-1) := Nat.Prime.even_sub_one hp h_gt_2.1
        have hq2: Even (q-1) := Nat.Prime.even_sub_one hq h_gt_2.2.1
        have hr2: Even (r-1) := Nat.Prime.even_sub_one hr h_gt_2.2.2
        have hpqr: 8 ∣ (p-1) * (q-1) * (r-1) := by
          obtain ⟨k, hk⟩ := hp2
          obtain ⟨m, hm⟩ := hq2
          obtain ⟨n, hn⟩ := hr2
          rw [hk, hm, hn]
          use k * m * n
          ring
        rw [← this] at hpqr
        contrapose hpqr
        native_decide

      . by_cases hp_eq_2 : p = 2
        . subst p
          simp at this
          have := h2 (q-1) (r-1) (Nat.Prime.even_sub_one hq (Ne.symm h_pq)) (Nat.Prime.even_sub_one hr (Ne.symm h_pr)) this
          simp at this
          rcases this with (rfl | rfl | rfl | rfl | rfl | rfl)
          . have : r = 667 := by omega
            subst r
            contrapose hr
            native_decide
          . have : r = 223 := by omega
            subst r n
            simp
          . have : r = 75 := by omega
            subst r
            contrapose hr
            native_decide
          . contrapose hq
            native_decide
          . have : r = 7 := by omega
            subst r n
            simp
          . contrapose hq
            native_decide

        . by_cases hq_eq_2 : q = 2
          . subst q
            simp at this
            have := h2 (p-1) (r-1) (Nat.Prime.even_sub_one hp h_pq) (Nat.Prime.even_sub_one hr (Ne.symm h_qr)) this
            simp at this
            rcases this with (rfl | rfl | rfl | rfl | rfl | rfl)
            . have : r = 667 := by omega
              subst r
              contrapose hr
              native_decide
            . have : r = 223 := by omega
              subst r n
              simp
            . have : r = 75 := by omega
              subst r
              contrapose hr
              native_decide
            . contrapose hp
              native_decide
            . have : r = 7 := by omega
              subst r n
              simp
            . contrapose hp
              native_decide

          . have hr_eq_2 : r = 2 := by
              simp at h_gt_2
              exact h_gt_2 hp_eq_2 hq_eq_2
            subst r
            simp at this
            have := h2 (p-1) (q-1) (Nat.Prime.even_sub_one hp hp_eq_2) (Nat.Prime.even_sub_one hq hq_eq_2) this
            simp at this
            rcases this with (rfl | rfl | rfl | rfl | rfl | rfl)
            . have : q = 667 := by omega
              subst q
              contrapose hq
              native_decide
            . have : q = 223 := by omega
              subst q n
              simp
            . have : q = 75 := by omega
              subst q
              contrapose hq
              native_decide
            . contrapose hp
              native_decide
            . have : q = 7 := by omega
              subst q n
              simp
            . contrapose hp
              native_decide

  . rintro (rfl | rfl | rfl)
    all_goals native_decide
