import Mathlib

theorem algebra_17104 : IsLeast {x | 0 < x ∧ 576 ∣ 400 * x} 36 := by
  constructor
  · -- Show that 36 is in the set
    constructor
    · norm_num
    · norm_num
  · -- Show that 36 is minimal
    intro y hy
    rcases hy with ⟨hy_pos, hy_div⟩
    by_contra h
    push_neg at h
    have h1 : y < 36 := h
    have h2 : 0 < y := hy_pos
    interval_cases y <;> norm_num at hy_div <;> omega