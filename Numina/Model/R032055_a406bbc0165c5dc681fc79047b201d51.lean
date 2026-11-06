import Mathlib

theorem number_theory_129543 :
    Set.ncard {n : ℕ | 0 < n ∧ 2 * n + 1 ∣ 8 * n + 50} = 1 := by
  have h1 : {n : ℕ | 0 < n ∧ 2 * n + 1 ∣ 8 * n + 50} = {11} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · -- Assume n > 0 and 2n + 1 divides 8n + 50, show n = 11
      intro h
      rcases h with ⟨hn_pos, hdiv⟩
      have h2 : (2 * n + 1 : ℕ) ∣ (8 * n + 50 : ℕ) := hdiv
      have h3 : (2 * n + 1 : ℕ) ∣ 46 := by
        have h3 : (2 * n + 1 : ℕ) ∣ (8 * n + 50 : ℕ) := h2
        have h4 : (2 * n + 1 : ℕ) ∣ (2 * n + 1 : ℕ) * 4 := by
          use 4
          all_goals ring
        have h5 : (2 * n + 1 : ℕ) ∣ (8 * n + 50 - (2 * n + 1) * 4 : ℕ) := by
          apply Nat.dvd_sub'
          · exact h3
          · exact h4
        have h6 : (8 * n + 50 - (2 * n + 1) * 4 : ℕ) = 46 := by
          omega
        rw [h6] at h5
        exact h5
      have h4 : n ≤ 22 := by
        by_contra h
        push_neg at h
        have h5 : (2 * n + 1 : ℕ) > 46 := by
          omega
        have h6 : (2 * n + 1 : ℕ) ≤ 46 := by
          exact Nat.le_of_dvd (by norm_num) h3
        linarith
      interval_cases n <;> norm_num at h2 hn_pos ⊢
      <;> omega
    · -- Show that n = 11 is in the set
      intro h
      rw [h]
      constructor
      · norm_num
      · norm_num
  rw [h1]
  simp