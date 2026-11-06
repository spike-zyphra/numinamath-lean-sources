import Mathlib

theorem algebra_11437 : IsLeast {x | x > 0 ∧ x % 3 = 0 ∧ x % 4 = 0 ∧ x % 6 = 0 ∧ x % 7 = 0} 84 := by
  constructor
  · -- Show 84 is in the set
    exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · -- Show no smaller positive integer is in the set
    intro x hx
    rcases hx with ⟨hx_pos, hx3, hx4, hx6, hx7⟩
    by_contra h
    push_neg at h
    have h1 : x < 84 := h
    interval_cases x <;> try { tauto } <;> omega