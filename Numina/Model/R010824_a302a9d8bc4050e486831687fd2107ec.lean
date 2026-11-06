import Mathlib

theorem algebra_11293 :
    IsLeast {x : ℕ | 0 < x ∧ 47 ∣ (2 * x) ^ 2 + 2 * 37 * 2 * x + 37 ^ 2} 5 := by
  constructor
  · -- Show that 5 is a valid element in the set, proving (0 < 5 ∧ 47 divides the expression when x = 5)
    constructor
    · -- Show that 0 < 5
      norm_num
    · -- Show that 47 divides the expression when x = 5
      norm_num
  · -- Show that for any y in the set, y >= 5
    intro y hy
    rcases hy with ⟨hy_pos, hy_div⟩
    by_contra h
    push_neg at h
    -- y must be less than 5
    have h1 : y < 5 := by 
      omega
    -- As y < 5 and y > 0, possible y values are 1, 2, 3, 4
    interval_cases y <;> norm_num at hy_div
    all_goals omega