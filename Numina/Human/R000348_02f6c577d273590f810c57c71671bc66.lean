import Mathlib

/-
  The solution to the system of equations $\left\{\begin{array}{l}{x+y=4}\\{2x-y=2}\end{array}\right.$ is ____.
-/
theorem algebra_9052 (x y : ℝ) : (x + y = 4 ∧ 2 * x - y = 2) ↔ (x = 2 ∧ y = 2) := by
  -- directly solve
  constructor
  · intros; repeat use by linarith
  · intros; simp_all; norm_num