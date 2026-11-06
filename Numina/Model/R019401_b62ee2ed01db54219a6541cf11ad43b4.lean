import Mathlib

theorem number_theory_178514 (p : ℕ) (hp : Nat.Prime p) :
    ∃ a b c, (a + p) * (b + p) * (c + p) = 1980 ↔
    (p = 2 ∧ (a = 0 ∧ b = 1 ∧ c = 4)) ∨
    (p = 2 ∧ (a = 0 ∧ b = 4 ∧ c = 1)) ∨
    (p = 2 ∧ (a = 1 ∧ b = 0 ∧ c = 4)) ∨
    (p = 2 ∧ (a = 1 ∧ b = 4 ∧ c = 0)) ∨
    (p = 2 ∧ (a = 4 ∧ b = 0 ∧ c = 1)) ∨
    (p = 2 ∧ (a = 4 ∧ b = 1 ∧ c = 0)) := by
  use 7, 8, 9
  constructor
  · -- Goal: (7 + p) * (8 + p) * (9 + p) = 1980 → RHS
    intro h
    have h1 : p ≤ 12 := by
      have h2 : p ^ 3 ≤ 1980 := by
        nlinarith
      have h3 : p ≤ 12 := by
        by_contra h
        push_neg at h
        have h6 : p ≥ 13 := by omega
        have h7 : p ^ 3 ≥ 2197 := by
          have h8 : p ≥ 13 := h6
          have h9 : p ^ 3 ≥ 13 ^ 3 := by
            apply Nat.pow_le_pow_of_le_left
            all_goals linarith
          norm_num at h9 ⊢
          all_goals linarith
        omega
      linarith
    interval_cases p <;> norm_num at h <;> tauto
  · -- Goal: RHS → (7 + p) * (8 + p) * (9 + p) = 1980
    rintro (h | h | h | h | h | h)
    · -- First disjunction
      rcases h with ⟨hp_eq, ha, hb, hc⟩
      omega
    · -- Second disjunction
      rcases h with ⟨hp_eq, ha, hb, hc⟩
      omega
    · -- Third disjunction
      rcases h with ⟨hp_eq, ha, hb, hc⟩
      omega
    · -- Fourth disjunction
      rcases h with ⟨hp_eq, ha, hb, hc⟩
      omega
    · -- Fifth disjunction
      rcases h with ⟨hp_eq, ha, hb, hc⟩
      omega
    · -- Sixth disjunction
      rcases h with ⟨hp_eq, ha, hb, hc⟩
      omega