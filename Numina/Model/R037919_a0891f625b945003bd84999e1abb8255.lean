import Mathlib

theorem number_theory_14599 :
    IsGreatest {p | Nat.Prime p ∧ (∃ n : ℕ, Nat.Prime n ∧ p = 2 ^ n - 1) ∧ p < 200} 127 := by
  constructor
  · -- Show 127 is in the set
    constructor
    · norm_num
    constructor
    · use 7
      constructor
      · norm_num
      · norm_num
    · norm_num
  · -- Show that 127 is greatest in the set
    intro p hp
    rcases hp with ⟨hp1, ⟨n, hn1, heq⟩, hp2⟩
    by_contra h
    push_neg at h
    have h1 : p > 127 := by linarith
    have h2 : 2 ^ n - 1 < 200 := by
      omega
    have h3 : 2 ^ n - 1 > 127 := by
      omega
    have h4 : 2 ^ n > 128 := by
      omega
    have h5 : n ≥ 8 := by
      by_contra h
      push_neg at h
      have h6 : n ≤ 7 := by
        omega
      have h7 : 2 ^ n ≤ 128 := by
        have h8 : n ≤ 7 := h6
        have h9 : 2 ^ n ≤ 2 ^ 7 := by
          apply Nat.pow_le_pow_of_le_right
          all_goals omega
        have h10 : 2 ^ 7 = 128 := by norm_num
        linarith
      linarith
    have h6 : n ≥ 8 := h5
    have h7 : 2 ^ n ≥ 256 := by
      have h8 : n ≥ 8 := h6
      have h9 : 2 ^ n ≥ 2 ^ 8 := by
        apply Nat.pow_le_pow_of_le_right (by norm_num) h8
      have h10 : 2 ^ 8 = 256 := by norm_num
      linarith
    have h8 : 2 ^ n < 201 := by
      omega
    linarith