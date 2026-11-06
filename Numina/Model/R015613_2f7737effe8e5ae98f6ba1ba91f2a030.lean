import Mathlib

theorem number_theory_112590 (n : ℕ) : (3 * n - 1) ∣ (7 * n + 5) ↔ n = 1 ∨ n = 4 := by
  constructor
  · -- Assume (3 * n - 1) ∣ (7 * n + 5), prove n = 1 ∨ n = 4
    intro h
    have h3 : (3 * n - 1) ∣ (7 * n + 5) := h
    -- Show that (3 * n - 1) divides 22
    have h5 : (3 * n - 1) ∣ 22 := by
      have h6 : (3 * n - 1) ∣ (7 * n + 5) := h3
      have h7 : (3 * n - 1) ∣ (3 * n - 1) := by
        use 1
        all_goals
          omega
      -- Compute 3*(7n + 5) - 7*(3n - 1) = 22
      have h8 : (3 * n - 1) ∣ (3 * (7 * n + 5) - 7 * (3 * n - 1)) := by
        apply Nat.dvd_sub'
        · -- Show that 3 * n - 1 divides 3 * (7 * n + 5)
          apply Dvd.dvd.mul_left
          exact h6
        · -- Show that 3 * n - 1 divides 7 * (3 * n - 1)
          apply Dvd.dvd.mul_left
          exact h7
      have h9 : 3 * (7 * n + 5) - 7 * (3 * n - 1) = 22 := by
        cases n with
        | zero =>
          omega
        | succ n =>
          cases n with
          | zero =>
            omega
          | succ n =>
            omega
      -- Rewrite h8 using h9
      have h10 : (3 * n - 1) ∣ 22 := by
        have h11 : (3 * n - 1) ∣ (3 * (7 * n + 5) - 7 * (3 * n - 1)) := h8
        rw [h9] at h11
        exact h11
      exact h10
    -- If (3 * n - 1) divides 22, then (3 * n - 1) ≤ 22
    have h7 : (3 * n - 1) ≤ 22 := by
      exact Nat.le_of_dvd (by norm_num) h5
    -- Check all possible n where (3 * n - 1) ≤ 22
    have h8 : n ≤ 8 := by
      by_contra h9
      push_neg at h9
      have h9 : n > 8 := by linarith
      have h10 : (3 * n - 1) > 22 := by
        omega
      linarith
    interval_cases n <;> norm_num at h5 h7 h <;> omega
  · -- Assume n = 1 ∨ n = 4, prove (3 * n - 1) ∣ (7 * n + 5)
    rintro (h | h)
    · -- Case n = 1
      rw [h]
      all_goals
        norm_num
    · -- Case n = 4
      rw [h]
      all_goals
        norm_num