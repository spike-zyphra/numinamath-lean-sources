import Mathlib

theorem algebra_11669 {r : ℝ} (hr : r > 0) (h : r^2 * (22 / 7) = 154) :

    2 * (22 / 7 ) * r + 2 = 46 := by 
  have hr2 : r^2 = 49 := by 
    nlinarith
  have hr' : r = 7 := by
    nlinarith [sq_nonneg r, hr]
  rw [hr']
  norm_num