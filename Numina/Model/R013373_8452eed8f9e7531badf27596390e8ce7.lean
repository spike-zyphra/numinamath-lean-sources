import Mathlib

theorem number_theory_188130 (n : ℕ) :
    Nat.Prime (1 + 4 * 9^(2 * n)) ↔ n = 0 := by

  constructor
  · -- Assume Nat.Prime (1 + 4 * 9^(2 * n)), prove n = 0
    intro h
    by_cases h1 : n > 0
    · -- If n > 0, prove contradiction.
      have h2 : n ≥ 1 := by linarith
      have h3 : (1 + 4 * 9 ^ (2 * n)) % 5 = 0 := by
        have h4 : ∀ k : ℕ, (1 + 4 * 9 ^ (2 * k)) % 5 = 0 := by
          intro k
          induction k with
          | zero =>
            norm_num
          | succ k ih =>
            simp [Nat.pow_add, pow_mul] at ih ⊢
            all_goals omega
        specialize h4 n
        simpa using h4
      have h4 : Nat.Prime (1 + 4 * 9 ^ (2 * n)) := h
      have h5 : n ≥ 1 := h2
      have h6 : (1 + 4 * 9 ^ (2 * n)) > 5 := by
        have h7 : 2 * n ≥ 2 := by
          omega
        have h8 : 9 ^ (2 * n) ≥ 81 := by
          have h7 : 9 ^ (2 * n) ≥ 9 ^ 2 := by
            apply Nat.pow_le_pow_of_le_right
            all_goals
            omega
          have h10 : 9 ^ 2 = 81 := by
            norm_num
          rw [h10] at *
          all_goals omega
        omega
      have h7 : (5 : ℕ) ∣ (1 + 4 * 9 ^ (2 * n)) := by
        omega
      have h8 : (5 : ℕ) = 1 ∨ (5 : ℕ) = (1 + 4 * 9 ^ (2 * n)) := by
        apply (Nat.dvd_prime h4).mp at h7
        tauto
      cases h8 with
      | inl h9 =>
        omega
      | inr h9 =>
        omega
    · -- n = 0
      have hn : n = 0 := by
        omega
      exact hn
  · -- Assume n = 0, prove Nat.Prime (1 + 4 * 9^(2 * n))
    rintro (rfl)
    norm_num