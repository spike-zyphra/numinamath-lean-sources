import Mathlib

theorem algebra_239946 (x y : ℝ) (hx : x > 0) (hy : y > 0)
    (h1 : x = 1 / 3) (h2 : x + y = 1 / (1 + 12 / 60)) :
    y = 1 / 2 := by
  have h3 : x + y = 5 / 6 := by
    norm_num at h2 ⊢
    linarith
  rw [h1] at h3
  linarith