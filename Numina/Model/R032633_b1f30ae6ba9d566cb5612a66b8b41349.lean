import Mathlib

theorem algebra_10358 (h : 1000 > 0) :
    IsLeast {n | ∃ x, x = 1000 / 2 ^ n ∧ x < 1} 10 := by
  constructor
  · -- Show that 10 is in the set
    use 1000 / 2 ^ 10
    all_goals norm_num
  · -- Show that no integer less than 10 is in the set
    intro n hn
    rcases hn with ⟨x, hx1, hx2⟩
    by_contra h'
    push_neg at h'
    -- Assume n < 10, prove contradiction
    have h1 : n < 10 := h'
    have h2 : x = 1000 / 2 ^ n := hx1
    have hx3 : x ≥ 1 := by
      rw [h2]
      interval_cases n <;> norm_num
    linarith