import Mathlib

theorem algebra_10042 : IsGreatest { x : ℕ | ∃ l w : ℕ, l * 330 + w * 450 ≤ 10000 ∧ x = l * w } 165 := by
  constructor
  · -- Show that 165 is in the set
    use 15, 11
    all_goals norm_num
  · -- Show that for all x in the set, x ≤ 165
    intro x hx
    rcases hx with ⟨l, w, hcost, heq⟩
    by_contra h
    push_neg at h
    have h1 : l * w > 165 := by
      omega
    have h2 : l ≤ 30 := by
      omega
    have h3 : w ≤ 22 := by
      omega
    interval_cases l <;> interval_cases w <;> omega