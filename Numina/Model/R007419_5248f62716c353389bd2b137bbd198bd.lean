import Mathlib

theorem algebra_15003 : IsLeast {p : ℕ | ∃ y, 0 < y ∧ p * 6 = y * 8 } 4 := by 
  constructor
  · -- Show 4 is in the set
    use 3
    all_goals norm_num
  · -- Show that any p in the set must be ≥ 4
    intro p hp
    rcases hp with ⟨y, hy, heq⟩
    by_contra h
    push_neg at h
    have h1 : p < 4 := by omega
    interval_cases p <;> omega