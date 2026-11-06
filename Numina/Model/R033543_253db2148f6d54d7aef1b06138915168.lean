import Mathlib

theorem number_theory_127919 (n : ℕ) : n + 1 ∣ n ^ 2 + 1 ↔ n = 0 ∨ n = 1 := by
  constructor
  · -- Assume n+1 ∣ n ^ 2 + 1, prove n=0 ∨ n=1
    intro h
    by_cases h1 : n > 1
    · -- Assume n > 1.
      have h3 : n + 1 ∣ 2 := by
        have h4 : n + 1 ∣ n ^ 2 + 1 := h
        have h5 : n + 1 ∣ (n + 1) * (n - 1) := by
          use n - 1
          all_goals
          ring_nf
        have h6 : n + 1 ∣ (n ^ 2 + 1) - ((n + 1) * (n - 1)) := by
          apply Nat.dvd_sub'
          · exact h4
          · exact h5
        have h7 : (n ^ 2 + 1) - ((n + 1) * (n - 1)) = 2 := by
          cases n with
          | zero =>
            omega 
          | succ n =>
            cases n with
            | zero =>
              omega
            | succ n =>
              simp [Nat.add_mul, Nat.mul_add, Nat.sub_sub, Nat.add_sub_cancel', mul_comm] at *
              <;> ring_nf at *
              <;> omega
        rw [h7] at h6
        exact h6
      have h7 : n + 1 ∣ 2 := h3
      have h8 : n + 1 ≤ 2 := by
        exact Nat.le_of_dvd (by norm_num) h7
      have h9 : n ≤ 1 := by
        omega
      omega
    · -- Assume n ≤ 1
      have h7 : n ≤ 1 := by omega
      have : n = 0 ∨ n = 1 := by
        interval_cases n <;> tauto
      tauto
  · -- Assume (n = 0 ∨ n = 1), prove (n + 1 ∣ n ^ 2 + 1).
    rintro (h | h)
    · -- Case n = 0.
      rw [h]
      all_goals norm_num
    · -- Case n = 1.
      rw [h]
      all_goals norm_num