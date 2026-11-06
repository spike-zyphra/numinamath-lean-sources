import Mathlib

lemma fifteenth_prime_ge_47 (S : Finset ℕ) (hS : S.card = 15)
    (hS1 : ∀ s ∈ S, Nat.Prime s) :
    ∃ s ∈ S, s ≥ 47 := by
  by_contra h
  push_neg at h
  have h3 : S.card ≤ 14 := by
    have h4 : S ⊆ (Finset.filter Nat.Prime (Finset.Iio 47)) := by
      intro s hs
      simp at hs ⊢
      exact ⟨h s hs, hS1 s hs⟩
    have h5 : S.card ≤ (Finset.filter Nat.Prime (Finset.Iio 47)).card := by
      apply Finset.card_le_card
      exact h4
    have h6 : (Finset.filter Nat.Prime (Finset.Iio 47)).card = 14 := by
      native_decide
    rw [h6] at h5
    exact h5
  omega

/- 15 positive integers, all less than 1998(and no one equal to 1), are relatively prime (no pair has a common factor > 1).
Show that at least one of them must be prime. -/
theorem number_theory_35958 (s : Finset ℕ)
  (h0 : s.card = 15)
  (h1 : ∀ m ∈ s, 1 < m)
  (h2 : ∀ m ∈ s, m < 1998)
  (h3 : ∀ m ∈ s, ∀ n ∈ s, m ≠ n → Nat.Coprime m n) :
  ∃ m ∈ s, Nat.Prime m := by
  -- Proof by contradiction: assume all numbers are not prime
  by_contra h
  push_neg at h

  -- Each number has a minimal prime factor, and the coprimality condition ensures different numbers have different minimal prime factors
  have distinct_minFac : ∀ m ∈ s, ∀ n ∈ s, m ≠ n → Nat.minFac m ≠ Nat.minFac n := by
    intro m hm n hn hmn heq
    have hp : Nat.Prime (Nat.minFac n) := by
      have : n ≠ 1 := ne_of_gt (h1 n hn)
      exact Nat.minFac_prime this
    have hdiv_m : Nat.minFac n ∣ m := by
      rw [← heq]; exact Nat.minFac_dvd m
    have hdiv_n : Nat.minFac n ∣ n := Nat.minFac_dvd n
    have : ¬Nat.Coprime m n := by
      intro hcoprime
      have : Nat.gcd m n = 1 := hcoprime
      have : Nat.minFac n ∣ 1 := by
        rw [← this]; exact Nat.dvd_gcd_iff.mpr ⟨hdiv_m, hdiv_n⟩
      have : Nat.minFac n ≤ 1 := Nat.le_of_dvd (by norm_num) this
      have : 2 ≤ Nat.minFac n := Nat.Prime.two_le hp
      omega
    exact this (h3 m hm n hn hmn)

  -- The mapping from s to minimal prime factors is injective
  have minFac_inj : ∀ m ∈ s, ∀ n ∈ s, Nat.minFac m = Nat.minFac n → m = n := by
    intro m hm n hn heq
    by_contra hmn
    exact distinct_minFac m hm n hn hmn heq

  -- All minimal prime factors form a set of 15 primes
  let prime_set := s.image Nat.minFac
  have h_card : prime_set.card = 15 := by
    rw [Finset.card_image_of_injOn]
    · exact h0
    · intro m hm n hn heq
      exact minFac_inj m hm n hn heq

  have all_prime : ∀ p ∈ prime_set, Nat.Prime p := by
    intro p hp
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hp
    have : m ≠ 1 := ne_of_gt (h1 m hm)
    exact Nat.minFac_prime this

  -- Apply auxiliary lemma: among 15 primes, at least one is ≥47
  obtain ⟨p, hp_in, hp_ge⟩ := fifteenth_prime_ge_47 prime_set h_card all_prime

  -- Find the corresponding number m
  obtain ⟨m, hm, hm_eq⟩ := Finset.mem_image.mp hp_in

  -- Case analysis
  by_cases h_eq : m = p
  · -- If m = p, then m is prime, contradiction
    have : Nat.Prime m := by
      rw [h_eq]
      exact all_prime p hp_in
    exact h m hm this
  · -- If m ≠ p, then m is composite and p = Nat.minFac m ≥ 47
    -- This means m ≥ p² ≥ 47² = 2209 > 1998, contradiction
    have : p ∣ m := by rw [← hm_eq]; exact Nat.minFac_dvd m
    have m_pos : 0 < m := by
      have : 1 < m := h1 m hm
      omega
    have : p ≤ m := Nat.le_of_dvd m_pos this
    have : p < m := Nat.lt_of_le_of_ne this (Ne.symm h_eq)

    -- m is composite, so m is not equal to its minimal prime factor p, therefore m ≥ 2p
    -- Actually, since m is not prime and p is its minimal prime factor, m must be at least p²
    have : m ≥ p * p := by
      -- This is a standard result: if n is composite and p is its minimal prime factor, then n ≥ p²
      by_contra h_not_ge
      push_neg at h_not_ge
      -- If m < p², then m = p * k where 1 < k < p
      have : m = p * (m / p) := by
        rw [Nat.mul_div_cancel_left']
        assumption
      have k_def : m / p < p := by nlinarith
      have k_gt_one : m / p > 1 := by
        by_contra h_not_gt
        push_neg at h_not_gt
        have k_pos : 0 < m / p := Nat.div_pos (by omega) (by omega)

        have : m = p := by
          have : m = p * (m / p) := (Nat.mul_div_cancel' ‹p ∣ m›).symm
          rw [this, show m / p = 1 by omega, mul_one]
        exact h_eq this
      -- So 1 < m/p < p, m/p has a prime factor q < p
      have : m / p ≠ 1 := ne_of_gt k_gt_one
      obtain ⟨q, hq_prime, hq_div⟩ := Nat.exists_prime_and_dvd this
      -- q divides m, contradicting that p is the minimal prime factor
      have : q ∣ m := by
        have : m = p * (m / p) := (Nat.mul_div_cancel' ‹p ∣ m›).symm
        rw [this]
        exact dvd_mul_of_dvd_right hq_div p
      have : q ≥ p := by
        rw [← hm_eq]
        exact Nat.minFac_le_of_dvd hq_prime.two_le this
      -- But q is a prime factor of m/p, so q ≤ m/p < p, contradiction
      have : q ≤ m / p := Nat.le_of_dvd (by omega) hq_div
      omega

    -- So m ≥ p² ≥ 47² = 2209 > 1998, contradiction
    have : p * p ≥ 47 * 47 := Nat.mul_le_mul hp_ge hp_ge
    have : m ≥ 47 * 47 := by omega
    have : 47 * 47 = 2209 := by norm_num
    have : 2209 > 1998 := by norm_num
    have : m < 1998 := h2 m hm
    omega
