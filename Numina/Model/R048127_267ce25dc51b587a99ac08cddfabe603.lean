import Mathlib

theorem algebra_214370 :
    IsLeast {x : ℕ | 0 < x ∧ ∃ k, (x + x + 3 + x + 6 + x + 9 + x + 12) = k^3} 19 := by
  constructor
  · -- Show 19 is in the set
    constructor
    · norm_num
    · -- Check existence of k
      use 5
      all_goals norm_num
  · -- Show no smaller element is in the set
    intro y hy
    rcases hy with ⟨hy_pos, ⟨k, hk⟩⟩
    by_contra h
    push_neg at h
    have h_eq : 5 * y + 30 = k^3 := by
      ring_nf at hk ⊢
      omega
    have eq1 : y < 19 := h
    have hk1 : k ≤ 4 := by
      by_contra h2
      push_neg at h2
      have h2' : k ≥ 5 := by omega
      have h3 : k ^ 3 ≥ 125 := by
        have h4 : k ≥ 5 := by omega
        have : k ^ 3 ≥ 5 ^ 3 := by
          apply Nat.pow_le_pow_of_le_left
          omega
        linarith
      nlinarith [show 5 * y + 30 ≤ 120 by omega, h_eq, h3]
    interval_cases k <;> omega