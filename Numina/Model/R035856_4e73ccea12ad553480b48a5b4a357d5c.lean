import Mathlib

theorem algebra_148926 (x p q r : ℝ × ℝ × ℝ)
    (hx : x = (6, -1, 7)) (hp : p = (1, -2, 0))
    (hq : q = (-1, 1, 3)) (hr : r = (1, 0, 4)) :
    x = -p - 3 * q + 4 * r := by
  rw [hx, hp, hq, hr]
  simp [Prod.ext_iff]
  all_goals norm_num