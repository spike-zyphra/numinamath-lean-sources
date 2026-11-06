import Mathlib

theorem inequalities_206714 (a1 a2 : ℝ) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2)
    (hsum : a1 + a2 = 1) :
    ∃ b1 b2 : ℝ, 0 ≤ b1 ∧ 0 ≤ b2 ∧ b1 + b2 = 1 ∧ (5 / 4 - a1) * b1 + 3 * (5 / 4 - a2) * b2 > 1 := by
  have ha2' : a2 = 1 - a1 := by linarith
  by_cases h : a1 < 1 / 8
  · -- Case 1: a1 < 1/8, set b1 = 1, b2 = 0
    use 1, 0
    constructor
    · -- Show 0 ≤ b1
      norm_num
    constructor
    · -- Show 0 ≤ b2
      norm_num
    constructor
    · -- Show b1 + b2 = 1
      norm_num
    · -- Show (5 / 4 - a1) * 1 + 3 * (5 / 4 - a2) * 0 > 1
      rw [show a2 = 1 - a1 by linarith]
      linarith
  · -- Case 2: a1 ≥ 1/8, set b1 = 0, b2 = 1
    use 0, 1
    constructor
    · -- Show 0 ≤ b1
      norm_num
    constructor
    · -- Show 0 ≤ b2
      norm_num
    constructor
    · -- Show b1 + b2 = 1
      norm_num
    · -- Show (5 / 4 - a1) * 0 + 3 * (5 / 4 - a2) * 1 > 1
      rw [show a2 = 1 - a1 by linarith]
      linarith