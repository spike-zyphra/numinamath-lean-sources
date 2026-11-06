import Mathlib

theorem algebra_275678 (l : ℝ) (hl : l = 20 * 18 * 5) (h : l / 25 = x) (hx : x > 0)
    (h1 : 2 * x = y) (hy : y > 0) :
    y = 144 := by
  have h2 : l = 1800 := by
    rw [hl]
    norm_num
  have hx2 : x = (l : ℝ) / 25 := by
    linarith [h]
  rw [h2] at hx2
  have hx3 : x = 72 := by
    norm_num at hx2 ⊢
    linarith
  have hy2 : y = 2 * x := by
    linarith
  rw [hx3] at hy2
  linarith