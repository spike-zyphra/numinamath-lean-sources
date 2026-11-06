import Mathlib

theorem number_theory_4971 (m n : ℕ) :
    m^2 + n^2 = 4034 ↔ (m=35 ∧ n=53) ∨ (m=53 ∧ n=35) := by 
  constructor
  · -- Assume left side
    intro h
    have h1 : m ≤ 63 := by
      nlinarith
    have h2 : n ≤ 63 := by
      nlinarith
    interval_cases m <;> interval_cases n <;> norm_num at h <;> tauto
  · -- Assume right side 
    rintro (h | h)
    · -- Case (35, 53)
      rcases h with ⟨h_m, h_n⟩
      rw [h_m, h_n]
      all_goals norm_num
    · -- Case (53, 35)
      rcases h with ⟨h_m, h_n⟩
      rw [h_m, h_n]
      all_goals norm_num