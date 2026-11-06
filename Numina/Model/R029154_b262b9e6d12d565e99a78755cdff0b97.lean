import Mathlib

theorem number_theory_50893 (n : ℕ) :
    IsSquare ((Nat.floor ((n + 3) / 4)) + (Nat.floor ((n + 5) / 4)) +
      (Nat.floor (n / 2)) + n ^ 2 + 3 * n + 3) := by
  have h2 : ∀ n : ℕ, (Nat.floor ((n + 3) / 4) ) + (Nat.floor ((n + 5) / 4) ) + (Nat.floor (n / 2) ) = n + 1 := by
    intro n
    by_cases h1 : n % 4 = 0
    · -- Case - n ≡ 0 mod 4.
      have h1' : ∃ k : ℕ, n = 4 * k := by
        refine' ⟨n / 4, by omega⟩
      rcases h1' with ⟨k, hk⟩
      rw [hk]
      all_goals
        simp [Nat.floor_eq_iff]
        <;> omega
    by_cases h2 : n % 4 = 1
    · -- Case - n ≡ 1 mod 4.
      have h2' : ∃ k : ℕ, n = 4 * k + 1 := by
        refine' ⟨(n - 1) / 4, by omega⟩
      rcases h2' with ⟨k, hk⟩
      rw [hk]
      all_goals
        simp [Nat.floor_eq_iff]
        <;> omega
    by_cases h3 : n % 4 = 2
    · -- Case - n ≡ 2 4.
      have h3' : ∃ k : ℕ, n = 4 * k + 2 := by
        refine' ⟨(n - 2) / 4, by omega⟩
      rcases h3' with ⟨k, hk⟩
      rw [hk]
      all_goals
        simp [Nat.floor_eq_iff]
        <;> omega
    · -- Case - n ≡ 3 4.
      have h4 : n % 4 = 3 := by omega
      have h4' : ∃ k : ℕ, n = 4 * k + 3 := by
        refine' ⟨(n - 3) / 4, by omega⟩
      rcases h4' with ⟨k, hk⟩
      rw [hk]
      all_goals
        simp [Nat.floor_eq_iff]
        <;> omega
  have h3 : (Nat.floor ((n + 3) / 4)) + (Nat.floor ((n + 5) / 4)) +
      (Nat.floor (n / 2)) + n ^ 2 + 3 * n + 3 = (n + 2) ^ 2 := by
    have h4 : (Nat.floor ((n + 3) / 4)) + (Nat.floor ((n + 5) / 4)) + (Nat.floor (n / 2)) = n + 1 := h2 n
    nlinarith [h4]
  rw [h3]
  exact ⟨n + 2, by ring⟩