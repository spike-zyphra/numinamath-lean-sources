import Mathlib

theorem algebra_98282 (x1 x2 y1 y2: ℝ)  (h1 : x1 * 2 = y1) (h2 : x2 * 6 = y2)
(h3 : y1 = 30) (h4 : y2 = 30) :
|x1 - x2| = 10 := by
  have hx1 : x1 = 15 := by
    linarith [h1, h3]
  have hx2 : x2 = 5 := by
    linarith [h2, h4]
  rw [hx1, hx2]
  norm_num [abs_of_nonneg]