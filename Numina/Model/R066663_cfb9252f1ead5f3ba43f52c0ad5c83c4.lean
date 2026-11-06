import Mathlib

theorem algebra_287935 :
    IsGreatest {z : ℕ | ∃ x y : ℕ, x > 0 ∧ y > 0 ∧ 27 * x + 35 * y ≤ 945 ∧ z = x * y} 234 := by
  constructor
  · -- Show that 234 is in the set
    use 18, 13
    all_goals norm_num
  · -- Show that no greater element is in the set
    intro z h
    rcases h with ⟨x, y, hx_pos, hy_pos, h_total, h_eq⟩
    by_contra h'
    push_neg at h'
    have h1 : x ≤ 35 := by
      omega
    have h2 : y ≤ 27 := by
      omega
    interval_cases x <;> interval_cases y
    <;> omega