import Mathlib

theorem algebra_263710 {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h1 : x * y = 1 / 9) (h2 : x * (y + 1) = 7 / 9) (h3 : y * (x + 1) = 5 / 18) :
    (x + 1) * (y + 1) = 35 / 18 := by
  have eq1 : x * (y + 1) = x * y + x := by ring
  rw [eq1] at h2
  rw [h1] at h2
  have eq_x : x = 2 / 3 := by
    nlinarith
  have eq_y : y = 1 / 6 := by 
    rw [eq_x] at h1
    nlinarith
  rw [eq_x, eq_y]
  norm_num