import Mathlib

theorem algebra_19236 : IsLeast {x : ℝ | x > 0 ∧ x < 2009 ∧ (2009 + x) ^ 2 - (2009 - x) ^ 2 ≥ 2009 ^ 2} (2009 / 4) := by
  constructor
  · -- Show that 2009/4 is in the set
    constructor
    · -- Show that 2009/4 is positive
      norm_num
    constructor
    · -- Show that 2009/4 < 2009
      norm_num
    · -- Show that (2009 + 2009/4)² - (2009 - 2009/4)² ≥ 2009²
      norm_num
  · -- Show that 2009/4 is the smallest element in the set
    intro x hx
    rcases hx with ⟨hx_pos, hx_lt, hineq⟩
    nlinarith [sq_nonneg (x - 2009 / 4)]