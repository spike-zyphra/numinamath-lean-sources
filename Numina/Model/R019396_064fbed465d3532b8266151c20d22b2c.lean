import Mathlib

theorem number_theory_168753 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h : (x * y * z) * (40 / 100) = 2 * (x / 2) * (y / 2) * (z / 2)) :
    x * y * z = 30 ∨ x * y * z = 60 := by
  have eq1 : x * y * z = 0 := by
    nlinarith
  have eq2 : x * y * z > 0 := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  linarith