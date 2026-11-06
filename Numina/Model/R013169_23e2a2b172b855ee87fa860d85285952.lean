import Mathlib

theorem algebra_4296 :
  IsLeast {n : ℕ | ∃ x y : ℕ, x > 0 ∧ y > 0 ∧ x * y + x + y = 2019 ∧ n = x + y} 119 := by
  constructor
  · -- Show that 119 is in the set
    use 100, 19
    all_goals norm_num
  · -- Show that 119 is the least
    intro n hn
    rcases hn with ⟨x, y, hx, hy, h_eq, hn⟩
    by_contra h
    push_neg at h
    have : x + y < 119 := by
      omega
    have h2 : x ≤ 117 := by
      omega
    have h3 : y ≤ 117 := by
      omega
    interval_cases x <;> omega