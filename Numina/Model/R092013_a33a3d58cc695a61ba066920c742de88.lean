import Mathlib

theorem number_theory_19469 : IsLeast {k | 0 < k ∧ ∃ n, 240 * k = n ^ 3} 900 := by
  constructor
  · -- Show 900 is in the set
    constructor
    · -- Show 900 is positive
      norm_num
    · -- Show that ∃ n, 240 * 900 = n ^ 3
      use 60
      all_goals norm_num
  · -- Show no smaller element is in the set
    intro k hk
    rcases hk with ⟨hk_pos, n, hn⟩
    by_contra h
    push_neg at h
    have h1 : k < 900 := by linarith
    have h2 : n ^ 3 < 60 ^ 3 := by
      nlinarith [hn, show 240 * k < 240 * 900 by linarith, mul_pos (show 0 < 240 by norm_num) hk_pos]
    have h3 : n < 60 := by
      by_contra h'
      push_neg at h'
      have h4 : n ≥ 60 := by linarith
      have h5 : n ^ 3 ≥ 60 ^ 3 := by
        have h8 : n ≥ 60 := h4
        have h9 : (n : ℕ) ≥ 60 := h8
        have h10 : (n : ℕ) ^ 3 ≥ 60 ^ 3 := by
          apply Nat.pow_le_pow_of_le_left
          all_goals omega
        linarith
      linarith
    have h4 : n ≤ 59 := by linarith
    interval_cases n <;> omega