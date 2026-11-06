import Mathlib

theorem algebra_11636 : IsLeast {x : ℕ | 0 < x ∧ 7 ∣ x ∧ 4 ∣ x} 28 := by
  constructor
  · -- Show 28 is in the set
    constructor
    · norm_num -- 0 < 28
    constructor
    · norm_num -- 7 divides 28
    · norm_num -- 4 divides 28
  · -- Show that if y is in the set, then y ≥ 28
    intro x hx
    rcases hx with ⟨hx_pos, hx_div_7, hx_div_4⟩
    -- If 7 divides x and 4 divides x, then 28 divides x
    -- Since x is positive and divisible by 28, so x ≥ 28
    omega