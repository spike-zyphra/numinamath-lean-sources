import Mathlib

theorem inequalities_232343 (m n : ℕ) :
    2^(m + n - 2) ≥ m * n := by
  by_cases h : m ≤ 1 ∨ n ≤ 1
  · -- Case 1: Either m ≤ 1 or n ≤ 1
    rcases h with (h1 | h2)
    · -- Subcase 1.1: m ≤ 1
      have h3 : m = 0 ∨ m = 1 := by
        have h4 : m ≤ 1 := h1
        interval_cases m <;> tauto
      rcases h3 with (rfl | rfl)
      · -- Subcase 1.1.1: m = 0
        simp
      · -- Subcase 1.1.2: m = 1
        have h5 : 2 ^ (1 + n - 2) ≥ 1 * n := by
          have h6 : 1 + n - 2 = n - 1 := by omega
          rw [h6]
          have h7 : ∀ k : ℕ, 2 ^ (k - 1) ≥ k := by
            intro k
            induction k with
            | zero =>
              simp
            | succ k ih =>
              cases k with
              | zero =>
                simp
              | succ k =>
                simp [pow_succ, pow_succ, pow_two, mul_add, mul_one] at ih ⊢
                omega
          have h8 : 2 ^ (n - 1) ≥ n := h7 n
          linarith
        linarith
    · -- Subcase 1.2: n ≤ 1
      have h4 : n = 0 ∨ n = 1 := by
        have h5 : n ≤ 1 := h2
        interval_cases n <;> tauto
      rcases h4 with (rfl | rfl)
      · -- Subcase 1.2.1: n = 0
        simp
      · -- Subcase 1.2.2: n = 1
        have h6 : 2 ^ (m + 1 - 2) ≥ m * 1 := by
          have h7 : m + 1 - 2 = m - 1 := by omega
          rw [h7]
          have h8 : ∀ k : ℕ, 2 ^ (k - 1) ≥ k := by
            intro k
            induction k with
            | zero =>
              simp
            | succ k ih =>
              cases k with
              | zero =>
                simp
              | succ k =>
                simp [pow_succ, pow_succ, pow_two, mul_add, mul_one] at ih ⊢
                omega
          have h9 : 2 ^ (m - 1) ≥ m := h8 m
          linarith
        linarith
  · -- Case 2: m ≥ 2 and n ≥ 2
    have hm : m ≥ 2 := by omega
    have hn : n ≥ 2 := by omega
    have h1 : 2 ^ (m - 1) ≥ m := by
      have h7 : ∀ k : ℕ, 2 ^ (k - 1) ≥ k := by
        intro k
        induction k with
        | zero =>
          simp
        | succ k ih =>
          cases k with
          | zero =>
            simp
          | succ k =>
            simp [pow_succ, pow_succ, pow_two, mul_add, mul_one] at ih ⊢
            omega
      exact h7 m
    have h2 : 2 ^ (n - 1) ≥ n := by
      have h7 : ∀ k : ℕ, 2 ^ (k - 1) ≥ k := by
        intro k
        induction k with
        | zero =>
          simp
        | succ k ih =>
          cases k with
          | zero =>
            simp
          | succ k =>
            simp [pow_succ, pow_succ, pow_two, mul_add, mul_one] at ih ⊢
            omega
      exact h7 n
    have h3 : 2 ^ (m + n - 2) = (2 ^ (m - 1)) * (2 ^ (n - 1)) := by
      rw [show m + n - 2 = (m - 1) + (n - 1) by omega]
      rw [pow_add]
    rw [h3]
    nlinarith [h1, h2, show (2 : ℕ) ^ (m - 1) ≥ 0 by omega, show (2 : ℕ) ^ (n - 1) ≥ 0 by omega, show m ≥ 0 by omega, show n ≥ 0 by omega]