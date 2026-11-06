import Mathlib

theorem algebra_137878 (x p q r : ℝ × ℝ × ℝ)
    (hx : x = (1, -4, 4)) (hp : p = (2, 1, -1))
    (hq : q = (0, 3, 2)) (hr : r = (1, -1, 1)) :
    x = -p + 3 * r := by
  rw [hx, hp, hr]
  simp only [Prod.ext_iff, Prod.mk.injEq]
  all_goals norm_num