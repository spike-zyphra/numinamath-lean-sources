import Mathlib

theorem number_theory_3856 :
    IsLeast {b : ℕ | 0 < b ∧ ∃ a : ℕ, 0 < a ∧ a^2 = 2023 * b} 7 := by
  constructor
  · -- Show that 7 is in the set
    constructor
    · -- Show 7 > 0
      norm_num
    · -- Show existence of such an a
      use 119
      constructor
      · -- Show 119 > 0
        norm_num
      · -- Show 119^2 = 2023 * 7
        norm_num
  · -- Show that 7 is the smallest
    intro b hb
    rcases hb with ⟨hb_pos, ⟨a, ⟨ha_pos, h⟩⟩⟩
    by_contra h1
    push_neg at h1
    -- bound `a` from above
    have h1' : a ≤ 150 := by
      nlinarith [show b < 7 from by omega, h]
    interval_cases b <;> 
      try { interval_cases a <;> omega }