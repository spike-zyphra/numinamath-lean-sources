import Mathlib

theorem algebra_608354 {x y z : ℝ} : (min x y) + z  = min (x+z)  (y+z) := by
  by_cases h : x ≤ y
  · -- Case where x ≤ y, so min x y = x
    have h1 : min x y = x := by
      apply min_eq_left
      linarith
    rw [h1]
    have h2 : min (x + z) (y + z) = x + z := by
      apply min_eq_left
      linarith
    rw [h2]
    all_goals linarith
  · -- Case where x > y, so min x y = y
    have h1 : min x y = y := by
      apply min_eq_right
      linarith
    rw [h1]
    have h2 : min (x + z) (y + z) = y + z := by
      apply min_eq_right
      linarith
    rw [h2]
    all_goals linarith