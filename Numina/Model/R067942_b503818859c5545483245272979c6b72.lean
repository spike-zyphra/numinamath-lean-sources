import Mathlib

theorem algebra_274100 (a b c : ℝ × ℝ)
    (ha : a = (1, 1)) (hb : b = (1, -1)) (hc : c = (-1, 2)) :
    c = (1 / 2 * a.1 - 3 / 2 * b.1, 1 / 2 * a.2 - 3 / 2 * b.2) := by
  rw [ha, hb, hc]
  all_goals norm_num