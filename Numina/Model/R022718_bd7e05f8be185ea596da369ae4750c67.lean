import Mathlib

theorem number_theory_116398 : (2019^(2020^2021)) % 10 = 1 := by 
  have h4 : ∃ (k : ℕ), (2020 ^ 2021 : ℕ) = 2 * k := by 
    have h2 : (2020 ^ 2021 : ℕ) % 2 = 0 := by 
      have h5 : ∀ (n : ℕ), (2020 ^ (n + 1) : ℕ) % 2 = 0 := by
        intro n 
        induction n with 
        | zero =>
          norm_num 
        | succ n ih =>
          have h6 : (2020 ^ (n + 1 + 1) : ℕ) % 2 = 0 := by
            have h7 : (2020 ^ (n + 1 + 1) : ℕ) = (2020 ^ (n + 1) ) * (2020) := by
              ring_nf 
            rw [h7]
            simp [Nat.mul_mod, show (2020 : ℕ) % 2 = 0 by norm_num] at *
            all_goals omega 
          exact h6 
      have h8 : (2020 ^ 2021 : ℕ) % 2 = 0 := by 
        have h9 : 2021 = 2020 + 1 := by
          omega 
        rw [h9]
        have h10 : (2020 ^ (2020 + 1) : ℕ) % 2 = 0 := h5 2020 
        exact h10 
      exact h8 
    have h5 : ∃ (k : ℕ), (2020 ^ 2021 : ℕ) = 2 * k := by 
      refine' ⟨(2020 ^ 2021) / 2, by 
        omega 
      ⟩ 
    exact h5 
  rcases h4 with ⟨k, hk⟩
  have h1 : ∀ (k : ℕ), (2019 ^ (2 * k) : ℕ) % 10 = 1 := by
    intro k
    induction k with 
    | zero =>
      norm_num 
    | succ k ih =>
      have h2 : (2019 ^ (2 * (k + 1) : ℕ) : ℕ) % 10 = 1 := by 
        have h3 : (2019 ^ (2 * (k + 1) : ℕ) : ℕ) = (2019 ^ (2 * k : ℕ) ) * (2019 ^ 2) := by
          ring_nf 
        rw [h3]
        simp [Nat.mul_mod, pow_two] at ih ⊢ 
        all_goals 
          norm_num at ih ⊢ 
          all_goals 
            omega 
      exact h2 
  have h7 : (2019 ^ (2 * k) : ℕ) % 10 = 1 := h1 k
  have h8 : (2019 ^ (2020 ^ 2021) ) % 10 = 1 := by 
    rw [show (2020 ^ 2021 : ℕ) = 2 * k by linarith [hk] ] 
    exact h7 
  exact h8