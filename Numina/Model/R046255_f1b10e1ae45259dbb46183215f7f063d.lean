import Mathlib

theorem number_theory_239934 {a b c : ℕ} (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (h : a^2 + b^2 = c^2) (hp : Nat.Prime a) :
    Odd b ∧ Even c ∨ Even b ∧ Odd c := by
  have h2 : a % 2 = 1 ∨ a = 2 := by
    by_cases ha2 : a > 2 
    · -- Assume a > 2
      have h3 : a % 2 = 1 := by
        by_contra h3
        push_neg at h3 
        have h4 : a % 2 = 0 := by 
          omega 
        have h5 : ¬ Nat.Prime a := by 
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ a by 
            omega 
          ) 
          all_goals 
          omega 
        exfalso 
        tauto 
      exact Or.inl h3 
    · -- Assume a ≤ 2 
      have h7 : a = 1 ∨ a = 2 := by 
        interval_cases a <;> omega 
      rcases h7 with (h1 | h2) 
      · -- Show contradiction: 1 is not prime 
        rw [h1] at hp 
        norm_num at hp 
      · -- Show that a = 2 
        exact Or.inr h2 
  rcases h2 with (h1 | ha2)
  · -- Now a % 2 = 1 
    have h3 : a % 2 = 1 := h1 
    have h5 : (a^2 : ℕ) % 2 = 1 := by 
      simp [Nat.pow_mod, h3]
    have h4 : (b^2 + c^2 : ℕ) % 2 = 1 := by 
      omega 
    by_cases h7 : b % 2 = 0 
    · -- Assume b is even 
      have h8 : (b^2) % 2 = 0 := by 
        simp [Nat.pow_mod, h7]
      have h9 : (c^2 : ℕ) % 2 = 1 := by 
        omega 
      have h10 : c % 2 = 1 := by 
        by_contra h10 
        push_neg at h10 
        have h11 : c % 2 = 0 := by 
          omega 
        have h12 : (c^2 : ℕ) % 2 = 0 := by 
          simp [Nat.pow_mod, h11]
        omega 
      have heven : Even b := ⟨b / 2, by omega⟩ 
      have hodd : Odd c := ⟨c / 2, by omega⟩ 
      right 
      exact ⟨heven, hodd⟩ 
    · -- Assume b is odd 
      have h7 : b % 2 = 1 := by 
        omega 
      have h8 : (b^2) % 2 = 1 := by 
        simp [Nat.pow_mod, h7]
      have h9 : (c^2 : ℕ) % 2 = 0 := by 
        omega 
      have h10 : c % 2 = 0 := by 
        by_contra h10 
        push_neg at h10 
        have h11 : c % 2 = 1 := by 
          omega 
        have h12 : (c^2 : ℕ) % 2 = 1 := by 
          simp [Nat.pow_mod, h11]
        omega 
      have heven : Even c := ⟨c / 2, by omega⟩ 
      have hodd : Odd b := ⟨b / 2, by omega⟩ 
      left 
      exact ⟨hodd, heven⟩ 
  · -- Now a = 2 
    have ha2' : a = 2 := by 
      omega 
    rw [show a = 2 by omega] at h 
    have h_eq : c ^ 2 = b ^ 2 + 4 := by 
      nlinarith 
    have h1 : c > b := by 
      nlinarith [sq_nonneg (c: ℕ), sq_nonneg (b: ℕ), h_eq]
    have h5 : b ≥ 1 := by 
      omega 
    have h6 : c ≤ b + 2 := by 
      nlinarith [sq_nonneg ((c: ℕ) - (b: ℕ) : ℤ), sq_nonneg ((c: ℕ) + (b: ℕ) : ℤ), 
        h_eq]
    by_cases h_eq1 : c = b + 1 
    · -- Assume c = b + 1 
      rw [h_eq1] at h_eq 
      have h100 : 2 * b = 3 := by 
        nlinarith 
      omega 
    by_cases h_eq2 : c = b + 2 
    · -- Assume c = b + 2 
      rw [h_eq2] at h_eq 
      have h100 : 4 * b = 0 := by 
        nlinarith 
      have h101 : b = 0 := by 
        omega 
      omega 
    have h7 : c = b + 1 ∨ c = b + 2 := by 
      have h8 : c ≤ b + 2 := h6 
      have h9 : c ≥ b + 1 := by 
        omega 
      omega 
    rcases h7 with (h7 | h7) 
    · -- Assume c = b + 1 
      exfalso 
      apply h_eq1 
      all_goals omega 
    · -- Assume c = b + 2 
      exfalso 
      apply h_eq2 
      all_goals omega