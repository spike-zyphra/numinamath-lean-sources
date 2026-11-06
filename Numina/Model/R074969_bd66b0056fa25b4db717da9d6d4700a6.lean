import Mathlib

theorem number_theory_23420 :
    IsLeast {n | ∃ k l, n = k^3 ∧ n = l^2 ∧ n > 64} 729 := by 
  constructor
  · -- Show 729 is in the set
    use 9, 27
    all_goals norm_num
  · -- Show 729 is the least
    intro n hn
    rcases hn with ⟨k, l, hk, hl, hn⟩
    by_contra h
    push_neg at h
    have h1 : k^3 < 729 := by
      linarith [hl, hk, h]
    have hk1 : k < 9 := by
      by_contra h2
      push_neg at h2
      have h3 : k^3 ≥ 729 := by
        have h4 : k ≥ 9 := by omega
        have h5 : k^3 ≥ 9^3 := by
          have h6 : k ≥ 9 := h4
          have h7 : k^3 ≥ 9^3 := by
            apply Nat.pow_le_pow_of_le_left h6 3
          linarith
        norm_num at h5 ⊢
        linarith
      linarith
    have hk2 : k > 4 := by
      by_contra h5
      push_neg at h5
      have h6 : k ≤ 4 := by omega
      have h7 : k^3 ≤ 64 := by
        have h8 : k^3 ≤ 4^3 := by
          have h9 : k ≤ 4 := h6
          have h10 : k^3 ≤ 4^3 := by
            apply Nat.pow_le_pow_of_le_left h9 3
          linarith
        norm_num at h8 ⊢
        linarith
      linarith [show k^3 > 64 from by linarith [hk, hl, hn]]
    have h2 : k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by omega
    rcases h2 with r | r | r | r
    · -- k = 5
      rw [r] at hk
      have h2 : l^2 = 125 := by linarith [hk, hl]
      have h3 : l ≤ 11 := by nlinarith
      interval_cases l <;> omega
    · -- k = 6
      rw [r] at hk
      have h2 : l^2 = 216 := by linarith [hk, hl]
      have h3 : l ≤ 14 := by nlinarith
      interval_cases l <;> omega
    · -- k = 7
      rw [r] at hk
      have h2 : l^2 = 343 := by linarith [hk, hl]
      have h3 : l ≤ 18 := by nlinarith
      interval_cases l <;> omega
    · -- k = 8
      rw [r] at hk
      have h2 : l^2 = 512 := by linarith [hk, hl]
      have h3 : l ≤ 22 := by nlinarith
      interval_cases l <;> omega