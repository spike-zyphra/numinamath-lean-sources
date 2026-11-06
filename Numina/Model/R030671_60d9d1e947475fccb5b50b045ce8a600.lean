import Mathlib

theorem number_theory_310167 :
    IsLeast {c : ℕ | ∃ a b : ℕ, a > 0 ∧ b > 0 ∧ a^2 + b^3 = c^4} 6 := by
  constructor
  · -- Show 6 is in the set
    use 28, 8
    all_goals norm_num
  · -- Show that no number less than 6 is in the set
    intro c hc
    rcases hc with ⟨a, b, ha, hb, h⟩
    by_contra h1
    push_neg at h1
    have h2 : c < 6 := h1
    have h3 : c ≤ 5 := by linarith
    have h4 : a ≤ 25 := by
      by_contra h4
      push_neg at h4
      have h7 : a ^ 2 ≤ c ^ 4 := by
        have h8 : b ^ 3 > 0 := by
          have hb_pos : b > 0 := hb
          have : b ≥ 1 := hb_pos
          have : b ^ 3 ≥ 1 ^ 3 := by
            apply Nat.pow_le_pow_left
            all_goals linarith
          linarith
        nlinarith [h, h8]
      have h7 : c ^ 4 ≤ 625 := by
        have hc5 : c ≤ 5 := by nlinarith
        have h8 : c ^ 4 ≤ 5 ^ 4 := by
          apply Nat.pow_le_pow_left
          all_goals
            omega
        norm_num at h8 ⊢
        linarith
      nlinarith [h4, h7]
    have h11 : b ≤ 8 := by
      by_contra h11
      push_neg at h11
      have h12 : b ^ 3 ≥ 729 := by
        have : b ≥ 9 := by linarith
        have h13 : b ^ 3 ≥ 9 ^ 3 := by
          apply Nat.pow_le_pow_left
          all_goals
            omega
        norm_num at h13 ⊢
        linarith
      have h7 : c ^ 4 ≤ 625 := by
        have hc5 : c ≤ 5 := by nlinarith
        have h8 : c ^ 4 ≤ 5 ^ 4 := by
          apply Nat.pow_le_pow_left
          all_goals
            omega
        norm_num at h8 ⊢
        linarith
      nlinarith [h, h12, h7]
    interval_cases c <;> interval_cases b <;> try { 
      omega
    } <;> try { 
      interval_cases a <;> omega 
    }