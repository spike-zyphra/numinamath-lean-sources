import Mathlib

theorem number_theory_256138 :
    IsLeast {N : ℕ | 0 < N ∧ N % 3 = 0 ∧ N % 4 = 0 ∧ N % 5 = 0 ∧ N % 6 = 0 ∧ N % 7 = 0} 420 := by
  constructor
  · -- Verify that 420 is in this set
    constructor
    · norm_num  -- 0 < (420 : ℕ)
    constructor
    · norm_num  -- (420 : ℕ) % 3 = 0
    constructor
    · norm_num  -- (420 : ℕ) % 4 = 0
    constructor
    · norm_num  -- (420 : ℕ) % 5 = 0
    constructor
    · norm_num  -- (420 : ℕ) % 6 = 0
    · norm_num  -- (420 : ℕ) % 7 = 0
  · -- Now prove minimality with a contradiction approach
    intro N h
    rcases h with ⟨hN_pos, hN_3, hN_4, hN_5, hN_6, hN_7⟩
    by_contra h'
    push_neg at h'
    interval_cases N <;> omega