import Mathlib

theorem algebra_14268 {x y : ℕ} (hx : x > 0) (hy : y > 0)
    (hxy : x - y = 6 ∨ y - x = 6) (hxy' : x * y = 135) :
    max x y = 15 := by
  rcases hxy with h | h
  · -- Case where $x - y = 6$
    have h1 : x = y + 6 := by
      omega
    rw [h1] at hxy'
    have h2 : y ≤ 15 := by
      nlinarith
      all_goals nlinarith
    interval_cases y <;> omega
    all_goals
      omega
  · -- Case where $y - x = 6$
    have h1 : y = x + 6 := by
      omega
    rw [h1] at hxy'
    have h2 : x ≤ 15 := by
      nlinarith
      all_goals nlinarith
    interval_cases x <;> omega
    all_goals
      omega