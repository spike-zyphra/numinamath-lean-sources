import Mathlib

theorem algebra_21938 (x1 x2 : ℝ) (y1 y2 : ℝ)
    (h1 : x1 = 3) (h2 : y1 = 5) (h3 : x2 = -6) (h4 : y2 = 2)
    (h5 : x3 = -10) (h6 : y3 = 4) :
    |(x1 + x2) / 2 - (x1 + x3) / 2| = 2 := by 
  have hx1 : x1 = 3 := h1
  have hx2 : x2 = -6 := h3
  have hx3 : x3 = -10 := h5
  rw [hx1, hx2, hx3]
  norm_num [abs_of_nonneg]