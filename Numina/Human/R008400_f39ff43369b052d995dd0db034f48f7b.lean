import Mathlib

theorem algebra_314130 :
    IsLeast {x | ∃ a b : ℤ, 0 < a ∧ a < 6 ∧ 0 < b ∧ b < 6 ∧ x = 2 * a - a * b} (-15) := by
  constructor
  · -- First, let's prove -15 is in the set by finding specific a, b that give -15
    use 5
    use 5
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Now, we need to prove that -15 is the least element in the set
    intro x h
    rcases h with ⟨a, b, ha1, ha2, hb1, hb2, hx⟩
    have ha3 : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 := by omega
    rcases ha3 with ha3 | ha3 | ha3 | ha3 | ha3
    · -- a = 1
      have hb3 : b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 := by omega
      rcases hb3 with hb3 | hb3 | hb3 | hb3 | hb3
      all_goals
        rw [ha3, hb3] at hx
        linarith
    · -- a = 2
      have hb3 : b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 := by omega
      rcases hb3 with hb3 | hb3 | hb3 | hb3 | hb3
      all_goals
        rw [ha3, hb3] at hx
        linarith
    · -- a = 3
      have hb3 : b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 := by omega
      rcases hb3 with hb3 | hb3 | hb3 | hb3 | hb3
      all_goals
        rw [ha3, hb3] at hx
        linarith
    · -- a = 4
      have hb3 : b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 := by omega
      rcases hb3 with hb3 | hb3 | hb3 | hb3 | hb3
      all_goals
        rw [ha3, hb3] at hx
        linarith
    · -- a = 5
      have hb3 : b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 := by omega
      rcases hb3 with hb3 | hb3 | hb3 | hb3 | hb3
      all_goals
        rw [ha3, hb3] at hx
        linarith