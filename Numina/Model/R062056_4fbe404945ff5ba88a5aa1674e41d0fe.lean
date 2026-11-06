import Mathlib

theorem algebra_271153 {x y : ℝ} (h : x - y = 86) (h' : x + y = 86 + 186) :
    max x y = 179 := by
  have h1 : x + y = 272 := by
    linarith
  have h2 : x = 179 := by
    linarith [h, h1]
  have h3 : y = 93 := by
    linarith [h2, h]
  rw [h2, h3]
  norm_num [max_eq_left]