import Mathlib

theorem number_theory_16766 :
    IsGreatest {x | 0 < x ∧ x < 500 ∧ 3 ∣ x ∧ 4 ∣ x} 492 := by
  constructor
  · -- Show that 492 is in the set
    exact ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
  · -- Show that 492 is the greatest element in the set
    intro x hx
    rcases hx with ⟨hx1, hx2, hx3, hx4⟩
    by_contra h
    push_neg at h
    have h1 : x < 500 := hx2
    interval_cases x <;> norm_num at *
    all_goals
      contradiction