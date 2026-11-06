import Mathlib

theorem algebra_97264 (P x : ℝ) (hP : 3 * (4 * x + 5 * Real.pi) = P) : 6 * (8 * x + 10 * Real.pi) = 4 * P := by
  have eq1 : 12 * x + 15 * Real.pi = P := by
    linarith [hP]

  have eq2 : 6 * (8 * x + 10 * Real.pi) = 48 * x + 60 * Real.pi := by
    ring

  have eq3 : 48 * x + 60 * Real.pi = 4 * (12 * x + 15 * Real.pi) := by
    ring

  rw [eq2, eq3, eq1]
  all_goals linarith