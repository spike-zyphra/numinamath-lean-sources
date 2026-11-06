import Mathlib

theorem number_theory_3807 : IsLeast {x : ℤ | x > 10 ∧ (x * (x - 20)) % 29 = 23} 16 := by
  constructor
  · -- Show that 16 satisfies the original conditions
    constructor
    · norm_num
    · norm_num
  · -- Show that 16 is the smallest such integer.
    intro x hx
    rcases hx with ⟨hx_gt, hx_cong⟩
    by_contra h
    push_neg at h
    have h1 : x < 16 := h
    have h2 : x > 10 := hx_gt
    have h3 : x = 11 ∨ x = 12 ∨ x = 13 ∨ x = 14 ∨ x = 15 := by 
      omega
    rcases h3 with (rfl | rfl | rfl | rfl | rfl)
    · -- x = 11
      norm_num at hx_cong
    · -- x = 12
      norm_num at hx_cong
    · -- x = 13
      norm_num at hx_cong
    · -- x = 14
      norm_num at hx_cong
    · -- x = 15
      norm_num at hx_cong