import Mathlib

theorem number_theory_779 :
    IsLeast {z : ℕ | ∃ x y, x > 0 ∧ y > 0 ∧ x * y = 108 ∧ z = x + y} 21 := by
  constructor
  · -- Show 21 is in the set.
    use 9, 12
    all_goals norm_num
  · -- Show if z in the set and z < 21, then z is invalid
    intro z h
    rcases h with ⟨x, y, hx, hy, hxy, hz⟩
    by_contra h'
    push_neg at h'
    have h1 : x ≤ 20 := by
      omega
    have h2 : y ≤ 20 := by
      omega
    interval_cases x <;> interval_cases y
      <;> omega