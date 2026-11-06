import Mathlib

theorem number_theory_53720 {n : ℕ} (hn : n ≠ 0) :
    Nat.lcm n (n - 30) = n + 1320 ↔ n = 165 := by
  constructor
  · -- Assume the equation holds, prove n = 165
    intro h_eq
    by_cases h : n > 30
    · -- Case n > 30
      have h1 : n - 30 > 0 := by
        omega
      -- Show that n divides 1320
      have h2 : n ∣ 1320 := by
        have h3 : n ∣ n + 1320 := by
          have h1 : n ∣ Nat.lcm n (n - 30) := by
            exact Nat.dvd_lcm_left n (n - 30)
          rw [h_eq] at h1
          exact h1
        have h4 : n ∣ (1320 : ℕ) := by
          have h5 : n ∣ (n + 1320 : ℕ) := h3
          have h6 : n ∣ (n : ℕ) := by
            exact dvd_refl n
          have h7 : n ∣ ((n + 1320) - n : ℕ) := by
            apply Nat.dvd_sub'
            · exact h5
            · exact h6
          have h8 : (n + 1320) - n = 1320 := by
            omega
          rw [h8] at h7
          exact h7
        exact h4
      -- Since n divides 1320, n ≤ 1320
      have h3 : n ≤ 1320 := by
        exact Nat.le_of_dvd (by omega) h2
      interval_cases n <;> norm_num at h_eq ⊢ <;> omega
    · -- Case n ≤ 30
      have h2 : n ≤ 30 := by
        omega
      interval_cases n <;> norm_num at h_eq ⊢ <;> omega
  · -- Assume n = 165, prove the equation
    intro h_eq
    rw [h_eq]
    all_goals norm_num