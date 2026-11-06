import Mathlib

theorem number_theory_177966 : ∃ a d : ℕ, ∀ n : ℕ, ∃ m : ℕ, a + d * n = m ∧ ¬∃ k : ℕ, m = k * (k - 1) / 2 := by 
  use 2  -- a = 2
  use 0  -- d = 0
  intro n
  use 2  -- m = 2
  constructor
  · -- Show that 2 + 0 * n = 2
    simp
  · -- Show that ¬∃ k : ℕ, 2 = k * (k - 1) / 2
    intro h
    rcases h with ⟨k, hk⟩
    have h_eq : k * (k - 1) / 2 = 2 := by
      omega
    have h1 : k ≤ 5 := by 
      by_contra h2
      push_neg at h2
      have h2 : k ≥ 6 := by omega
      have eq1 : k * (k - 1) ≥ 30 := by
        have eq4 : k ≥ 6 := by omega
        have eq5 : k - 1 ≥ 5 := by omega
        nlinarith [show k ≥ 6 by omega, show k - 1 ≥ 5 by omega]
      have eq2 : k * (k - 1) / 2 ≥ 15 := by
        have h2 : k * (k - 1) ≥ 30 := by
          have eq4 : k ≥ 6 := by omega
          have eq5 : k - 1 ≥ 5 := by omega
          nlinarith [show k ≥ 6 by omega, show k - 1 ≥ 5 by omega]
        have h3 : k * (k - 1) / 2 ≥ 30 / 2 := by
          apply Nat.div_le_div
          all_goals
            omega
        omega
      omega
    interval_cases k <;> norm_num at h_eq