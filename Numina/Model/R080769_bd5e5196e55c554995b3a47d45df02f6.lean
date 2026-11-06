import Mathlib

theorem inequalities_262550 : (5 / 24 : ℚ) > 1 / 6 ∧ (5 / 24 : ℚ) < 1 / 4 := by
  constructor
  · -- Show that $\frac{5}{24}$ is greater than $\frac{1}{6}$.
    norm_num
  · -- Show that $\frac{5}{24}$ is smaller than $\frac{1}{4}$.
    norm_num