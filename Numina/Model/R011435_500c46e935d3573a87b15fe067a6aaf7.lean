import Mathlib

theorem number_theory_627675 (p q m n : ℕ)
    (hp₁ : Nat.Prime p) (hq₂ : Nat.Prime q)
    (hp₂ : p = m + n) (hq₃ : q = m * n) :
    (p ^ p + q ^ q) / (m ^ n + n ^ m : ℚ) = 31 / 3 := by
  have h1 : m > 0 := by
    by_contra h
    push_neg at h
    have h2 : m = 0 := by
      omega
    rw [h2] at hq₃
    have hq₃' : q = 0 := by
      nlinarith
    rw [hq₃'] at hq₂
    norm_num at hq₂
  -- Show n > 0
  have h4 : n > 0 := by
    by_contra h
    push_neg at h
    have h5 : n = 0 := by
      omega
    rw [h5] at hp₂ hq₃
    have hp₂' : p = m := by
      omega
    have hq₃' : q = 0 := by
      nlinarith
    rw [hq₃'] at hq₂
    norm_num at hq₂
  -- Show that either m=1 or n=1
  have h5 : m ≥ 1 := h1
  have h6 : n ≥ 1 := h4
  have h7 : m = 1 ∨ n = 1 := by
    by_contra h
    push_neg at h
    have h8 : m ≥ 2 := by 
      omega
    have h9 : n ≥ 2 := by 
      omega
    have h10 : q = m * n := hq₃
    have h11 : ¬ Nat.Prime q := by
      rw [h10]
      apply Nat.not_prime_mul (by omega) (by omega)
    contradiction
  rcases h7 with (hm | hn)
  · -- Case m = 1
    have hm1 : m = 1 := hm
    have hp₂' : p = 1 + n := by 
      rw [hp₂]
      simp [hm1]
    have hq₃' : q = n := by
      rw [hq₃]
      simp [hm1]
    by_cases h8 : n ≤ 2
    · -- Case n ≤ 2
      interval_cases n <;> norm_num [hm1, hp₂', hq₃'] at hp₁ hq₂ ⊢ <;> norm_num
    · -- Case n > 2
      have hn1 : n > 2 := by
        omega
      have hn2 : n ≥ 3 := by
        omega
      have h8 : n % 2 = 0 ∨ n % 2 = 1 := by
        omega
      rcases h8 with (h8 | h8)
      · -- Case n % 2 = 0
        have h9 : ¬ Nat.Prime n := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ n by omega) (by omega) (by omega)
        have h10 : Nat.Prime n := by 
          rw [hq₃'] at hq₂ 
          exact hq₂
        contradiction
      · -- Case n % 2 = 1
        have hp₂'' : p = n + 1 := by 
          omega
        have hp₁' : Nat.Prime p := hp₁ 
        have h11 : p % 2 = 0 := by
          have : n % 2 = 1 := h8
          omega
        have h12 : ¬ Nat.Prime p := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by omega) (by omega)
        have h13 : Nat.Prime p := hp₁ 
        contradiction
  · -- Case n = 1
    have hn1 : n = 1 := hn
    have hp₂' : p = m + 1 := by 
      rw [hp₂]
      simp [hn1]
    have hq₃' : q = m := by
      rw [hq₃]
      simp [hn1]
    by_cases h8 : m ≤ 2
    · -- Case m ≤ 2
      interval_cases m <;> norm_num [hn1, hp₂', hq₃'] at hp₁ hq₂ ⊢ <;> norm_num
    · -- Case m > 2
      have hm1 : m > 2 := by
        omega
      have hm2 : m ≥ 3 := by 
        omega
      have h8 : m % 2 = 0 ∨ m % 2 = 1 := by
        omega
      rcases h8 with (h8 | h8)
      · -- Case m % 2 = 0 
        have h9 : ¬ Nat.Prime m := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ m by omega) (by omega) (by omega)
        have h10 : Nat.Prime m := by 
          rw [hq₃'] at hq₂ 
          exact hq₂
        contradiction
      · -- Case m % 2 = 1 
        have hp₂'' : p = m + 1 := by 
          omega
        have hp₁' : Nat.Prime p := hp₁ 
        have h11 : p % 2 = 0 := by
          have : m % 2 = 1 := h8
          omega
        have h12 : ¬ Nat.Prime p := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by omega) (by omega)
        have h13 : Nat.Prime p := hp₁ 
        contradiction