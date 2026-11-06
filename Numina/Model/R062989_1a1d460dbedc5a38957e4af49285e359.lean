import Mathlib

theorem algebra_234324 :
    IsLeast {n | ∃ x y, x > 0 ∧ y > 0 ∧ x * y = 240 ∧ n = x + y} 31 := by
  constructor
  · -- Show that 31 belongs to the set
    use 15, 16
    all_goals norm_num
  · -- Show that 31 is the minimum
    intro n hn
    rcases hn with ⟨x, y, hx, hy, hxy, hn⟩
    by_contra h
    push_neg at h
    have h1 : x ≤ 30 := by omega
    have h2 : y ≤ 30 := by omega
    interval_cases x <;> interval_cases y
    <;> omega