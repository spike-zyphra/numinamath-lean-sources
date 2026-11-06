import Mathlib

theorem algebra_80837
    (a b c : ℝ)
    (h1 : 3 * a + 4 * b = 3 * c)
    (h2 : 4 * a - 3 * b = 4 * c) :
    a ^ 2 + b ^ 2 = c ^ 2 := by
  have eq1 : a = c := by
    linarith [h1, h2]
  -- From h1 solve for b
  have eq2 : b = 0 := by
    rw [eq1] at h1
    linarith
  rw [eq1, eq2]
  all_goals ring