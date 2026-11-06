import Mathlib

theorem inequalities_308999 (x y : ℝ) (h : 3 * abs (x + 1) + 2 * abs (y - 1) ≤ 6) :
    2 * x - 3 * y ≤ 4 := by
  cases' abs_cases (x + 1) with h1 h1
  · -- Case where |x + 1| = x + 1
    cases' abs_cases (y - 1) with h2 h2
    · -- Case where |y - 1| = y - 1
      linarith
    · -- Case where |y - 1| = 1 - y
      linarith
  · -- Case where |x + 1| = -(x + 1)
    cases' abs_cases (y - 1) with h2 h2
    · -- Case where |y - 1| = y - 1
      linarith
    · -- Case where |y - 1| = 1 - y
      linarith