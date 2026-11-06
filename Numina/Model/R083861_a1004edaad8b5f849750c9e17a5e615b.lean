import Mathlib

theorem other_138951 :
    IsLeast {n | ∃ k, n = k ∧ 35 * n ≥ 420} 12 := by
  constructor
  · -- Show that 12 is in the set
    use 12
    all_goals norm_num
  · -- Show that 12 is the smallest in the set
    intro n hn
    rcases hn with ⟨k, rfl, hk⟩
    omega