import Mathlib

theorem number_theory_4605 : IsLeast {b : ℕ | 0 < b ∧ ∃ a : ℕ, 0 < a ∧ a^3 = 360 * b^2} 45 := by
  constructor
  · -- Show that 45 is in the set
    constructor
    · norm_num
    · use 90
      all_goals norm_num
  · -- Show that 45 is the minimum
    intro b hb
    rcases hb with ⟨hb_pos, a, ha_pos, h_eq⟩
    by_contra h
    push_neg at h
    have h1 : b ≤ 44 := by
      omega
    have h7 : a ≤ 89 := by
      have h8 : a ^ 3 ≤ 360 * (44 : ℕ) ^ 2 := by
        have h9 : b ≤ 44 := by linarith
        have h10 : b ^ 2 ≤ (44 : ℕ) ^ 2 := by nlinarith
        nlinarith [show 0 ≤ (360 : ℕ) by norm_num, 
                  show 0 ≤ (b ^ 2 : ℕ) by positivity]
      -- a^3 ≤ 700960, so a ≤ 89.
      have h11 : a ≤ 89 := by
        by_contra h
        push_neg at h
        have h12 : a ≥ 90 := by linarith
        have h13 : a ^ 3 ≥ 729000 := by
          have h14 : a ≥ 90 := h12
          have h15 : a ^ 3 ≥ 90 ^ 3 := by
            apply Nat.pow_le_pow_of_le_left h14 3
          norm_num at h15 ⊢
          linarith
        nlinarith
      linarith
    interval_cases b <;> interval_cases a <;> omega