import Mathlib

theorem algebra_263247 (x y : ℝ) (hx : x > 0) (hy : y > 0)
    (hjill : x = (1 / 2) / 6 + (1 / 2) / 12) (hjack : y = (1 / 3) / 5 + (2 / 3) / 15) :
    x / y = 9 / 8 := by
  have hx_eq : x = 1 / 8 := by
    rw [hjill]
    norm_num
  have hy_eq : y = 1 / 9 := by
    rw [hjack]
    norm_num
  rw [hx_eq, hy_eq]
  all_goals norm_num