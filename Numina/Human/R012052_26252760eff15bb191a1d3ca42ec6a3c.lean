import Mathlib
open Nat Real 

/-3. Given the equation $x^{4}-p x^{3}+q=0$ has an integer root, find the prime numbers $p$ and $q$.-/
theorem number_theory_600025 : ∀ (p q : ℕ), Nat.Prime p → Nat.Prime q →
  (∃ x : ℤ, x^4 - p * x^3 + q = 0) → p = 3 ∧ q = 2 := by
  -- Introduce variables and assumptions.
  intros p q hp hq hroot
  -- Extract the integer root $x$.
  obtain ⟨x, hx⟩ : ∃ x : ℤ, x^4 - p * x^3 + q = 0 := hroot
  -- From the equation $x^4 - p x^3 + q = 0$, derive $q = x^3 (p - x)$.
  have hq_eq : (q : ℤ) = x^3 * ((p : ℤ) - x) := by
    have h : (q : ℤ) = x^3 * (p : ℤ) - x^4 := by
      rw [← sub_eq_zero]
      rw [← hx]
      ring
    have h_eq : x^3 * (p : ℤ) - x^4 = x^3 * ((p : ℤ) - x) := by
      rw [mul_sub]
      simp [pow_succ]
    rwa [h_eq] at h
  -- $x$ divides $q$.
  have h_div : x ∣ (q : ℤ) := by
    use (x^2 * (p - x))
    rw [hq_eq]
    ring
  -- Since $q$ is prime and $x$ is an integer dividing $q$, $x = ±1$ or $x = ±q$.
  have h_cases : x = 1 ∨ x = -1 ∨ x = q ∨ x = -q := by
    have hq_pos : q > 0 := Nat.Prime.pos hq
    have hq_dvd : ∃ n : ℕ, (q : ℤ) = n := by
      use q
    obtain ⟨n, hn⟩ := hq_dvd
    have h_dvd : x ∣ n := by
      rw [hn] at h_div
      exact h_div
    have h_n_pos : n > 0 := by linarith
    have h_x_cases : (∃ m : ℕ, x = m ∧ m ∣ n) ∨ (∃ m : ℕ, x = -m ∧ m ∣ n) := by
      let k := Int.natAbs x
      have h_x_k : x = k ∨ x = -k := by omega
      rcases h_x_k with (hx_eq_k | hx_eq_neg_k)
      · left
        use k
        have h_k_dvd : (k : ℤ) ∣ n := by
          rw [← hx_eq_k]
          exact h_dvd
        norm_cast at h_k_dvd
      · right
        use k
        have h_k_dvd : (k : ℤ) ∣ n := by
          rw [hx_eq_neg_k] at h_dvd
          exact Int.neg_dvd.mp h_dvd
        norm_cast at h_k_dvd
    rcases h_x_cases with (⟨m, hx_eq_m, hm_dvd⟩ | ⟨m, hx_eq_neg_m, hm_dvd⟩)
    · have hm_cases : m = 1 ∨ m = n := by
        have h_n_eq_q : n = q := by omega
        rw [h_n_eq_q]
        rw [h_n_eq_q] at hm_dvd
        have h_m_dvd_q : m ∣ q := hm_dvd
        exact (Nat.dvd_prime hq).mp h_m_dvd_q
      rcases hm_cases with (hm_eq_1 | hm_eq_n)
      · left
        rwa [hm_eq_1, Int.ofNat_one] at hx_eq_m
      · omega
    · have hm_cases : m = 1 ∨ m = n := by
        have h_n_eq_q : n = q := by omega
        rw [h_n_eq_q]
        rw [h_n_eq_q] at hm_dvd
        have h_m_dvd_q : m ∣ q := hm_dvd
        exact (Nat.dvd_prime hq).mp h_m_dvd_q
      rcases hm_cases with (hm_eq_1 | hm_eq_n)
      · omega
      · omega
  -- Case analysis for $x = ±1, ±q$.
  rcases h_cases with (hx_eq_1 | hx_eq_neg_1 | hx_eq_q | hx_eq_neg_q)
  -- Case $x = 1$.
  · have h_pq : p = q + 1 := by
      rw [hx_eq_1] at hq_eq
      omega
    have h_p_prime : Nat.Prime (q + 1) := by
      rw [← h_pq]
      exact hp
    have h_pq_prime : q = 2 ∧ p = 3 := by
      have hq_2 : q = 2 := by
        have hq_cases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q ≥ 7 := by
          have hq_ge_2 : q ≥ 2 := Nat.Prime.two_le hq
          rcases Nat.eq_or_lt_of_le hq_ge_2 with (hq_eq_2 | hq_gt_2)
          · left
            exact hq_eq_2.symm
          · have hq_ge_3 : q ≥ 3 := by linarith
            rcases Nat.eq_or_lt_of_le hq_ge_3 with (hq_eq_3 | hq_gt_3)
            · right
              left
              exact hq_eq_3.symm
            · have hq_ge_5 : q ≥ 5 := by
                apply Nat.Prime.five_le_of_ne_two_of_ne_three
                · exact hq
                · nlinarith [hq_gt_3]
                · nlinarith [hq_gt_3]
              rcases Nat.eq_or_lt_of_le hq_ge_5 with (hq_eq_5 | hq_gt_5)
              · right
                right
                left
                exact hq_eq_5.symm
              · right
                right
                right
                have hq_ge_7 : q ≥ 7 := by
                  have hq_ge_6 : q ≥ 4 := by linarith
                  have hq_ne_6 : q ≠ 6 := by
                    intro q6
                    rw [q6] at hq
                    contradiction
                  omega
                exact hq_ge_7
        rcases hq_cases with (hq_eq_2 | hq_eq_3 | hq_eq_5 | hq_ge_7)
        · exact hq_eq_2
        · have h_contr : Nat.Prime (3 + 1) := by rw [hq_eq_3] at h_p_prime;exact h_p_prime
          contradiction
        · have h_contr : Nat.Prime (5 + 1) := by rw [hq_eq_5] at h_p_prime;exact h_p_prime
          contradiction
        · have h_contr : ¬ Nat.Prime (q + 1) := by
            apply Nat.not_prime_of_dvd_of_ne
            · have hq_odd : Odd q := by
                apply Nat.Prime.odd_of_ne_two
                · exact hq
                · linarith
              have h_q_plus_one_even : Even (q + 1) := by
                apply Nat.even_add_one.mpr
                exact (Nat.not_even_iff_odd.mpr hq_odd)
              have : 2 ∣ (q + 1) := by exact even_iff_two_dvd.mp h_q_plus_one_even
              exact this
            · linarith
            · linarith
          contradiction
      have hp_eq_3 : p = 3 := by
        rw [h_pq, hq_2]
      exact ⟨hq_2, hp_eq_3⟩
    exact h_pq_prime.symm
  -- Case $x = -1$.
  · have h_contr : False := by
      rw [hx_eq_neg_1] at hq_eq
      simp at hq_eq
      norm_cast at hq_eq
      have hq_neg : (q : ℤ) < 0 := by
        rw [hq_eq]
        simp
        have hp_pos : (p : ℤ) > 0 := by
          exact Nat.cast_pos.mpr (Nat.Prime.pos hp)
        linarith
      have hq_pos : (q : ℤ) > 0 := by
        exact Nat.cast_pos.mpr (Nat.Prime.pos hq)
      linarith
    contradiction
  -- Case $x = q$.
  · have h_contr : (q : ℤ)^2 ∣ 1 := by
      rw [hx_eq_q] at hq_eq
      have h_q_nonzero : (q : ℤ) ≠ 0 := by
        have hq_pos : q > 0 := Nat.Prime.pos hq
        exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq_pos)
      have h_div : (q : ℤ) * 1 = (q : ℤ) * ((q : ℤ)^2 * ((p : ℤ) - (q : ℤ))) := by
        rw [mul_one]
        have : (q : ℤ)^3 = (q : ℤ) * (q : ℤ)^2 := by ring
        rw [← mul_assoc,← this]
        exact hq_eq
      have h_cancel : 1 = (q : ℤ)^2 * ((p : ℤ) - (q : ℤ)) := by
        apply Int.eq_of_mul_eq_mul_left h_q_nonzero h_div
      use (p : ℤ) - (q : ℤ)
    have h_false : False := by
      have hq_pos : q > 1 := Nat.Prime.one_lt hq
      have hq_square : q^2 > 1 := by
        nlinarith
      have h_dvd_one : q^2 ∣ 1 := by
        norm_cast at h_contr
      have h_eq_one : q^2 = 1 := by exact Nat.dvd_one.mp h_dvd_one
      linarith
    contradiction
  -- Case $x = -q$.
  · have h_contr : (q : ℤ)^2 ∣ 1 := by
      rw [hx_eq_neg_q] at hq_eq
      have h_q_nonzero : (q : ℤ) ≠ 0 := by
        have hq_pos : q > 0 := Nat.Prime.pos hq
        exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq_pos)
      have h_div : (q : ℤ) * 1 = (q : ℤ) * (-(q : ℤ)^2 * ((p : ℤ) + (q : ℤ))) := by
        rw [mul_one]
        have : (-(q : ℤ))^3 = (q : ℤ) * (-(q : ℤ)^2) := by ring
        rw [this,mul_assoc] at hq_eq
        have : (p : ℤ) + (q : ℤ) = (p : ℤ) - - (q : ℤ) := by ring
        rw [← this] at hq_eq
        exact hq_eq
      have h_cancel : 1 = -(q : ℤ)^2 * ((p : ℤ) + (q : ℤ)) := by
        apply Int.eq_of_mul_eq_mul_left h_q_nonzero h_div
      have h_dvd : (q : ℤ)^2 ∣ 1 := by
        use -(p : ℤ) - (q : ℤ)
        rw [h_cancel]
        ring
      exact h_dvd
    have h_false : False := by
      have hq_pos : q > 1 := Nat.Prime.one_lt hq
      have hq_square : q^2 > 1 := by
        nlinarith
      have h_dvd_one : q^2 ∣ 1 := by
        norm_cast at h_contr
      have h_eq_one : q^2 = 1 := by exact Nat.dvd_one.mp h_dvd_one
      linarith
    contradiction
