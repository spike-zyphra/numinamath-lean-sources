import Mathlib

theorem algebra_162837 {x y : ℝ} (h : x > 0) (h' : y > 0)
    (h1 : x * 7 = y * 4) (h2 : y = x + 15 / 100) :
    4 * y = 1.40 := by
  rw [h2] at h1 -- substitute equation h2 into h1
  have hx : x = (1 : ℝ) / 5 := by
    linarith
  have hy : y = (7 : ℝ) / 20 := by
    rw [hx] at h2
    linarith
  rw [hy]
  norm_num