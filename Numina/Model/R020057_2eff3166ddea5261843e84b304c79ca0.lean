import Mathlib

theorem number_theory_122623 (n : ℕ) (hn : n ≠ 0) : (n^2 + 1) ∣ n + 1 ↔ n = 1 := by
  constructor
  · -- Assume h: (n ^ 2 + 1) ∣ (n + 1)
    intro h
    by_cases h1 : n > 1
    · -- n > 1
      have h2 : n ^ 2 + 1 > n + 1 := by
        nlinarith [show n > 1 by linarith, h1]
      have h3 : n ^ 2 + 1 ≤ n + 1 := by
        exact Nat.le_of_dvd (by omega) h
      nlinarith
    · -- n ≤ 1
      have h4 : n = 1 := by
        have h5 : n ≤ 1 := by linarith
        have h6 : n ≥ 1 := by omega
        have h7 : n = 1 := by linarith
        exact h7
      exact h4
  · -- Assume n = 1
    intro h
    rw [h]
    all_goals norm_num