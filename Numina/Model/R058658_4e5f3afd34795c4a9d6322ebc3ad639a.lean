import Mathlib

theorem algebra_13000 :
    IsLeast {a : ℕ | 0 < a ∧ 4 ∣ a ∧ 14 ∣ a} 28 := by
  constructor
  · -- Show that 28 belongs to the set
    show 0 < (28 : ℕ) ∧ 4 ∣ (28 : ℕ) ∧ 14 ∣ (28 : ℕ)
    constructor
    · norm_num
    constructor
    · norm_num
    all_goals norm_num
  · -- Show that 28 is the smallest such element
    intro a h
    rcases h with ⟨ha_pos, h4, h14⟩
    omega