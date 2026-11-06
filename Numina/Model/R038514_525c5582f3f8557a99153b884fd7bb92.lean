import Mathlib

theorem number_theory_93871 :
    IsLeast {x : ℕ | 0 < x ∧ ∃ N, 1260 * x = N ^ 3} 7350 := by
  constructor
  · -- Show 7350 is in the set.
    constructor
    · -- Show 7350 > 0.
      norm_num
    · -- Show that there exists N such that 1260 * 7350 = N ^ 3.
      use 210
      all_goals
        norm_num
  · -- Show there is no smaller positive integer x in the set
    intro x hx
    rcases hx with ⟨hx1, ⟨N, hN⟩⟩
    by_contra h
    push_neg at h
    have h2 : N ^ 3 < 210 ^ 3 := by
      have h3 : 1260 * x < 1260 * 7350 := by 
        omega
      have h4 : N ^ 3 < 1260 * 7350 := by
        linarith [hN]
      nlinarith
    have h3 : N < 210 := by
      by_contra h4
      push_neg at h4
      have h5 : N ^ 3 ≥ 210 ^ 3 := by
        have h6 : N ≥ 210 := by
          omega
        have h7 : N ^ 3 ≥ 210 ^ 3 := by
          apply Nat.pow_le_pow_of_le_left h6 3
        linarith
      linarith
    have h4 : N < 210 := h3
    have h5 : N ≤ 209 := by
      omega
    interval_cases N <;> omega