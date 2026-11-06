import Mathlib

theorem number_theory_4555
    (x y : ℝ) :
    max x y + min x y = x + y := by
  cases le_or_lt x y with
  | inl h =>
    -- case x y where x ≤ y
    have h1 : max x y = y := by
      apply max_eq_right
      all_goals linarith
    have h2 : min x y = x := by
      apply min_eq_left
      all_goals linarith
    rw [h1, h2]
    all_goals linarith
  | inr h =>
    -- case y x where y < x
    have h1 : max x y = x := by
      apply max_eq_left
      all_goals linarith
    have h2 : min x y = y := by
      apply min_eq_right
      all_goals linarith
    rw [h1, h2]
    all_goals linarith