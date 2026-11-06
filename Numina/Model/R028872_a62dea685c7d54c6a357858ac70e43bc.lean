import Mathlib

theorem algebra_179896 (a b : ℕ) :
    2 * (a + b) = a * b ↔ (a = 6 ∧ b = 3) ∨ (a = 0 ∧ b = 0) ∨ (a = 4 ∧ b = 4) ∨ (a = 3 ∧ b = 6) := by
  constructor
  · -- Forward: 2(a+b) = a * b implies the solutions
    rintro h
    have h1 : a ≤ 7 := by
      by_contra h2
      push_neg at h2
      have h2' : b ≤ 6 := by
        nlinarith [h, h2]
      interval_cases b <;> omega
    have h2 : b ≤ 7 := by
      by_contra h3
      push_neg at h3
      have h4 : a ≤ 6 := by
        nlinarith [h, h3]
      interval_cases a <;> omega
    interval_cases a <;> interval_cases b
      <;> norm_num at h ⊢ <;> tauto
  · -- Backward: solutions satisfy 2(a+b) = a * b
    rintro (h | h | h | h)
    · -- First solution
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- Second solution
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- Third solution
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- Fourth solution
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num