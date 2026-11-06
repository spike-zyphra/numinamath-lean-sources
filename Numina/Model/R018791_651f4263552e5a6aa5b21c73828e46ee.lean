import Mathlib

theorem number_theory_283675 :
    IsLeast {x : ℕ | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ x = 2 * a^5 ∧ x = 3 * b^2} 15552 := by
  constructor
  · -- Show that 15552 is in the set
    use 6, 72
    all_goals
      norm_num
  · -- Show that 15552 is minimal
    intro x hx
    rcases hx with ⟨a, b, ha, hb, hx1, hx2⟩
    by_contra h
    push_neg at h
    have h1 : x < 15552 := h
    have h2 : a ≤ 5 := by
      by_contra h2
      push_neg at h2
      have h3 : a ^ 5 ≥ 6 ^ 5 := by
        have h4 : a ≥ 6 := by omega
        have h5 : a ^ 5 ≥ 6 ^ 5 := by
          apply Nat.pow_le_pow_of_le_left
          linarith
        linarith
      have h6 : 2 * a ^ 5 ≥ 15552 := by
        nlinarith [show 2 * 6 ^ 5 = 15552 from by norm_num, h3]
      nlinarith [show 2 * a ^ 5 = x from by linarith [hx1], h1]
    have h3 : b ≤ 71 := by
      by_contra h3
      push_neg at h3
      have h4 : b ≥ 72 := by omega
      have h5 : b ^ 2 ≥ 72 ^ 2 := by
        have h6 : b ≥ 72 := h4
        nlinarith
      have h6 : 3 * b ^ 2 ≥ 15552 := by
        nlinarith [show 3 * 72 ^ 2 = 15552 from by norm_num, h5]
      nlinarith [hx2, h1]
    interval_cases a <;> try { 
      omega
    }
    <;> try { 
      interval_cases b <;> omega 
    }