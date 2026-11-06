import Mathlib

theorem algebra_4726 {x y : ℤ} (hx : x > y) (h1 : x = 3 * y - 17) (h2 : x + y = 3 * (x - y)) :
    x * y = 578 := by 
  rw [h1] at h2 -- substitute x = 3*y - 17 in h2
  have eq1 : 4 * y - 17 = 6 * y - 51 := by 
    linarith [h2]
  have hy : y = 17 := by
    linarith [eq1]
  have hx' : x = 34 := by
    rw [hy] at h1
    linarith
  rw [hx', hy]
  norm_num