import Mathlib

-- Supplement a theorem not provided in lean$4.15$.
lemma Nat.minFac_prime_iff {n : ℕ} : Prime (minFac n) ↔ n ≠ 1 := by
  refine ⟨?_, minFac_prime⟩
  rintro h rfl
  exact not_prime_one h

/-2. Two-digit numbers are written on the board. Each number is composite, but any two numbers are coprime. What is the maximum number of numbers that can be written?-/
theorem number_theory_126507 :
    IsGreatest {n | ∃ (S : Finset ℕ), (∀ m ∈ S, ¬Nat.Prime m ∧ 10 ≤ m ∧ m ≤ 99) ∧
    (∀ m ∈ S, ∀ n ∈ S, m ≠ n → Nat.Coprime m n) ∧ S.card = n} 4 := by
  let s := {n | ∃ (S : Finset ℕ), (∀ m ∈ S, ¬Nat.Prime m ∧ 10 ≤ m ∧ m ≤ 99) ∧
    (∀ m ∈ S, ∀ n ∈ S, m ≠ n → Nat.Coprime m n) ∧ S.card = n}
  refine ⟨?_, ?_⟩
  -- Verify the upper bound is achievable.
  have h_reachable : ∃ T : Finset ℕ, (∀ m ∈ T, ¬Nat.Prime m ∧ 10 ≤ m ∧ m ≤ 99) ∧
      (∀ m ∈ T, ∀ n ∈ T, m ≠ n → Nat.Coprime m n) ∧ T.card = 4 := by
    let T : Finset ℕ := {25, 26, 33, 49}
    exists T
  obtain ⟨T, hT⟩ := h_reachable
  simp [s]
  exact ⟨T, hT⟩
  intro n hn
  simp [s] at hn
  obtain ⟨S, hS, hS1, hn⟩ := hn
  rw [← hn]
  -- Define the set of primes less than $10$.
  have h_primes : Finset.filter Nat.Prime (Finset.range 8) = {2, 3, 5, 7} := by rfl
  -- Each prime factor $2$, $3$, $5$, $7$ appears in at most one number's factorization.
  have h_prime_unique : ∀ p ∈ Finset.filter Nat.Prime (Finset.range 8), ∀ m ∈ S, ∀ n ∈ S, m ≠ n → p ∣ m → ¬p ∣ n := by
    intro p hp m hm n hn hmn hpm
    by_contra hpn
    have h_coprime : Nat.Coprime m n := hS1 m hm n hn hmn
    rw [Nat.coprime_iff_gcd_eq_one] at h_coprime
    have h_p_prime : Nat.Prime p := by simp [Finset.mem_filter] at hp; exact hp.2
    have h_p_prime' : Prime p := by exact Nat.prime_iff.mp h_p_prime
    have h_p_dvd_mn : p ∣ m * n := dvd_mul_of_dvd_left hpm n
    have : p ∣ m.gcd n := Nat.dvd_gcd hpm hpn
    have h_p_dvd_one : p ∣ 1 := by rw [← h_coprime ]; exact this
    have h_p_not_dvd_one : ¬ p ∣ 1 := Prime.not_dvd_one h_p_prime'
    contradiction
  -- If card of $S$ greater than $4$, then there exists a number whose all prime factors greater than or equals $11$.
  have h_card_bound : S.card ≤ (Finset.filter Nat.Prime (Finset.range 8)).card := by
    by_contra h_contra
    push_neg at h_contra
    have h_primes_card : (Finset.filter Nat.Prime (Finset.range 8)).card = 4 := by
      rw [h_primes]
      simp
    have h_card_S : S.card ≥ 5 := by omega
    have h_exists_large : ∃ m ∈ S, ∀ p, Nat.Prime p → p ∣ m → p ≥ 11 := by
      by_contra h_abs
      push_neg at h_abs
      let primes := Finset.filter Nat.Prime (Finset.range 8)
      let f : ℕ → ℕ := Nat.minFac
      have h_maps_to : Set.MapsTo f ↑S ↑primes := by
        intro m hm
        obtain ⟨p, hp_prime, hp_dvd, hp_lt11⟩ := h_abs m hm
        have h_min_le : f m ≤ p := Nat.minFac_le_of_dvd hp_prime.two_le hp_dvd
        have h_f_lt11 : f m < 11 := lt_of_le_of_lt h_min_le hp_lt11
        have h_f_prime : Nat.Prime (f m) := Nat.minFac_prime_iff.mpr (by nlinarith[(hS m hm).2.1])
        have h_f_ge2 : f m ≥ 2 := h_f_prime.two_le
        -- By contradiction, when fm greater than $7$, all are not prime, leading to contradiction.
        have h_f_le7 : f m ≤ 7 := by
          by_contra h
          push_neg at h
          have h_ge8 : f m ≥ 8 := h
          have h_cases : f m = 8 ∨ f m = 9 ∨ f m = 10 := by omega
          cases h_cases
          · have : f m = 8 := by assumption
            have h8 : Nat.Prime 8 := by rw [← this]; exact h_f_prime
            have : ¬ Nat.Prime 8 := by norm_num
            contradiction
          · have : f m = 9 ∨ f m = 10 := by assumption
            cases this
            · have : f m = 9 := by assumption
              have h8 : Nat.Prime 9 := by rw [← this]; exact h_f_prime
              have : ¬ Nat.Prime 9 := by norm_num
              contradiction
            · have : f m = 10 := by assumption
              have h8 : Nat.Prime 10 := by rw [← this]; exact h_f_prime
              have : ¬ Nat.Prime 10 := by norm_num
              contradiction
        have h_range : f m < 8 := by omega
        simp [primes, Finset.mem_filter, Finset.mem_range]
        exact ⟨h_range, h_f_prime⟩
      have hc : primes.card < S.card := by nlinarith
      -- Apply pigeonhole principle to get contradiction.
      obtain ⟨m, hm, n, hn, hmn_ne, hf_eq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hc h_maps_to
      let p := f m
      have hp_in : p ∈ primes := h_maps_to hm
      have hp_prime : Nat.Prime p := (Finset.mem_filter.mp hp_in).2
      have hp_dvd_m : p ∣ m := Nat.minFac_dvd m
      have hp_dvd_n : p ∣ n := by unfold p;rw [hf_eq]; exact Nat.minFac_dvd n
      have h_not : ¬ p ∣ n := h_prime_unique p hp_in m hm n hn hmn_ne hp_dvd_m
      contradiction
    obtain ⟨m, hm, h_m_large⟩ := h_exists_large
    have h_m_composite : ¬Nat.Prime m := (hS m hm).1
    have h_m_bound : m ≤ 99 := (hS m hm).2.2
    -- $m$ is composite and prime factors greater than $11$, derive $m$ greater than $121$.
    have h_m_large_prime : m ≥ 121 := by
      let p := Nat.minFac m
      have hp_dvd : p ∣ m := Nat.minFac_dvd m
      have hp_prime : Nat.Prime p := Nat.minFac_prime_iff.mpr (by nlinarith[(hS m hm).2.1])
      have hp_ge11 : p ≥ 11 := h_m_large p hp_prime hp_dvd
      have h_sq : p ^ 2 ≤ m := by
        unfold p
        exact Nat.minFac_sq_le_self (by nlinarith[(hS m hm).2.1]) (hS m hm).1
      nlinarith
    linarith
  exact h_card_bound
