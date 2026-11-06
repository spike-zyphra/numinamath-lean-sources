import Mathlib

theorem algebra_20592 {n : ℕ} (hn : n > 0) :
    IsLeast {n | 0 < n ∧ (n % 1 = 0 ∧ n % 3 = 0 ∧ n % 5 = 0 ∧ n % 7 = 0)} 105 := by
  constructor
  · -- Show 105 is in the set
    constructor
    · norm_num
    · -- Show 105 % 1 = 0 ∧ 105 % 3 = 0 ∧ 105 % 5 = 0 ∧ 105 % 7 = 0
      norm_num
  · -- Show 105 is minimal
    intro m hm
    rcases hm with ⟨hm_pos, ⟨h1, h3, h5, h7⟩⟩
    -- We need to show that m >= 105
    -- Since m % 3 = 0, m % 5 = 0, and m % 7 = 0, m must be divisible by 3, 5, and 7
    -- As 3, 5, and 7 are coprime, m must be divisible by 3 * 5 * 7 = 105
    -- Hence m >= 105
    by_contra h
    push_neg at h
    interval_cases m <;> omega