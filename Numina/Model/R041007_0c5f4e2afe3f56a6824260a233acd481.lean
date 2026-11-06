import Mathlib

theorem number_theory_159997 (n : ℕ) :
    n > 0 ∧ n - 1 ∣ n ^ 3 + 4 ↔ n = 2 ∨ n = 6 := by
  constructor
  · -- Assume n > 0 and n - 1 divides n^3 + 4, prove n = 2 or n = 6
    intro h
    rcases h with ⟨hn_pos, hdiv⟩
    by_cases h2 : n > 1
    · -- n > 1
      have h3 : n - 1 ∣ 5 := by
        have h4 : n - 1 ∣ n ^ 3 + 4 := hdiv
        have h5 : n - 1 ∣ (n - 1) * (n ^ 2 + n + 1) := by 
          use n ^ 2 + n + 1
          all_goals ring_nf <;> omega
        have h6 : n - 1 ∣ (n ^ 3 + 4) - ((n - 1) * (n ^ 2 + n + 1)) := by 
          apply Nat.dvd_sub'
          · exact h4
          · exact h5
        have h7 : (n ^ 3 + 4) - ((n - 1) * (n ^ 2 + n + 1)) = 5 := by
          cases n with
          | zero =>
            omega -- contradicts n > 0
          | succ n =>
            cases n with
            | zero =>
              all_goals omega
            | succ n =>
              simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul]
              <;> ring_nf <;> omega
        rw [h7] at h6
        exact h6
      have h4 : n - 1 = 1 ∨ n - 1 = 5 := by
        have h5 : n - 1 ∣ 5 := h3
        have h6 : n - 1 ≤ 5 := by
          exact Nat.le_of_dvd (by norm_num) h5
        have h7 : n - 1 ≥ 1 := by
          omega
        interval_cases h : n - 1 <;> tauto
      rcases h4 with (h4 | h4)
      · -- n - 1 = 1
        have h2' : n = 2 := by 
          omega
        left
        exact h2'
      · -- n - 1 = 5
        have h6' : n = 6 := by
          omega
        right
        exact h6'
    · -- n ≤ 1, so n = 1
      have h3 : n = 1 := by
        omega
      rw [h3] at hdiv
      norm_num at hdiv
      all_goals omega
  · -- Assume n = 2 or n = 6, prove n > 0 and n - 1 divides n^3 + 4
    rintro (h | h)
    · -- n = 2
      rw [h]
      constructor
      · norm_num
      · norm_num
    · -- n = 6
      rw [h]
      constructor
      · norm_num
      · norm_num