import Mathlib

theorem algebra_85320 :
    IsLeast {k : ℝ | ∃ a b, 0 < k ∧ a + b = k ∧ a * b = k} 4 := by
  constructor
  · -- Let's show that 4 is in the set
    use (2 : ℝ), (2 : ℝ)
    constructor
    · norm_num -- k is positive
    constructor
    · norm_num -- a + b = k
    · norm_num -- a * b = k
  · -- Let's show that if k is in the set, then k ≥ 4
    intro k hk
    rcases hk with ⟨a, b, hk_pos, h_eq_sum, h_eq_mul⟩
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - k)]