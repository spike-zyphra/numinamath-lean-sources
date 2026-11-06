import Mathlib

theorem number_theory_113178 (n : ℕ) :
    ∃ k, ∀ m ∈ Finset.range n, ¬Nat.Prime (k + m) := by 
  use (n + 1).factorial + 2
  intro m hm
  have h1 : m < n := by 
    simp at hm ⊢
    all_goals omega 
  by_cases h : n < 1 
  · -- n = 0, Finset.range 0 is empty
    have h2 : n = 0 := by 
      omega 
    rw [h2] at hm 
    simp at hm 
  · -- Assume n ≥ 1 
    have hn : n ≥ 1 := by 
      omega 
    have h5 : m + 2 ∣ (n + 1).factorial + 2 + m := by 
      have h51 : m + 2 ≤ n + 1 := by 
        omega 
      have h4 : m + 2 ∣ (n + 1).factorial := by 
        apply Nat.dvd_factorial 
        all_goals 
          omega 
      have h5a : m + 2 ∣ (2 + m) := by 
        have h64 : 2 + m = m + 2 := by 
          omega 
        rw [h64] 
        all_goals 
          use 1 
          all_goals 
            try tauto 
      have h5b : m + 2 ∣ ((n + 1).factorial + 2 + m) := by 
        have h4a : m + 2 ∣ (n + 1).factorial := h4 
        have h6a : m + 2 ∣ (2 + m) := h5a 
        have h7a : m + 2 ∣ ((n + 1).factorial + (2 + m)) := by 
          apply Nat.dvd_add 
          exact h4a 
          exact h6a 
        have h39 : (n + 1).factorial + 2 + m = (n + 1).factorial + (2 + m) := by 
          omega 
        rw [h39] 
        exact h7a 
      exact h5b 
    have hx1 : (n + 1).factorial + 2 + m > 1 := by 
      have h2a : m < n := h1 
      have hn0 : n ≥ 1 := hn 
      have h1a : (n + 1).factorial ≥ 1 := by 
        apply Nat.factorial_pos 
      omega 
    have hx2 : m + 2 > 1 := by 
      omega 
    have hx3 : m + 2 < (n + 1).factorial + 2 + m := by 
      have hn3 : n ≥ 1 := hn 
      have h14 : (n + 1).factorial > 0 := by 
        have : (n + 1) ≥ 1 := by omega 
        positivity 
      omega 
    have h9 : ¬ Nat.Prime ((n + 1).factorial + 2 + m) := by
      apply Nat.not_prime_of_dvd_of_lt h5 
      all_goals 
        omega 
    exact h9