import Mathlib

theorem algebra_314130 :
    IsLeast {x | ∃ a b : ℤ, 0 < a ∧ a < 6 ∧ 0 < b ∧ b < 6 ∧ x = 2 * a - a * b} (-15) := by
  constructor
  · -- Show that -15 is in the set
    use 5, 5
    all_goals norm_num
  · -- Show that -15 is the minimal element in the set
    intro x hx
    rcases hx with ⟨a, b, ha1, ha2, hb1, hb2, h_eq⟩
    by_contra h
    push_neg at h
    have h1 : a > 0 := by linarith
    have h2 : a < 6 := by linarith
    have h3 : b > 0 := by linarith
    have h4 : b < 6 := by linarith
    interval_cases a <;> interval_cases b <;> omega