import Mathlib

theorem number_theory_4318 :
  IsLeast {b : ℕ | ∃(a : ℕ), 0 < a ∧ 0 < b ∧ a ≠ b ∧ a^5 = 21 * b^2} 441 := by
  constructor
  · -- Show 441 is indeed in the set
    use 21
    all_goals
      norm_num
  · -- Show that 441 is the minimum
    intro b hb
    rcases hb with ⟨a, ha_pos, hb_pos, hab, hab_eq⟩
    by_contra h
    push_neg at h
    have h1 : b < 441 := h
    have h2 : a ≤ 21 := by
      by_contra h2
      push_neg at h2
      have h3 : a ^ 5 > 21 * b ^ 2 := by
        have h4 : a ≥ 22 := by linarith
        have h5 : b ≤ 440 := by linarith
        have h6 : a ^ 5 ≥ 22 ^ 5 := by
          have h7 : a ≥ 22 := by linarith
          have h8 : a ^ 5 ≥ 22 ^ 5 := by
            apply Nat.pow_le_pow_of_le_left
            linarith
          linarith
        have h7 : b ^ 2 ≤ 440 ^ 2 := by
          nlinarith
        nlinarith [h6, h7]
      nlinarith [h3, hab_eq]
    have h3 : b < 441 := h1
    interval_cases a <;> try { 
      omega
    }
    all_goals
      try { 
        interval_cases b <;> omega 
      }