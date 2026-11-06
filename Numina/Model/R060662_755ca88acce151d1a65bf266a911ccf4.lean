import Mathlib

theorem calculus_12383 : 3 * (fun (x y : ℝ) => (x, y)) 2 (-8) - 2 * (fun (x y : ℝ) => (x, y)) 1 (-7) = (fun (x y : ℝ) => (x, y)) 4 (-10) := by
  simp [Prod.ext_iff]
  all_goals norm_num