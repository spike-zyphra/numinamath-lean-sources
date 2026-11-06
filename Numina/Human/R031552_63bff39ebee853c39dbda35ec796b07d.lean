import Mathlib

theorem algebra_261949 {x y : ℝ} (h : x + y = x * y) (hx : x = 987654321) :
    y = 1 + 1 / 987654320 := by
  have h1 : (x - 1) * (y - 1) = 1 := by
    linarith [h]
  rw [hx] at h1
  have h2 : (987654321 : ℝ) - 1 = 987654320 := by norm_num
  rw [h2] at h1
  have hy : y = 1 + 1 / 987654320 := by
    linarith
  exact hy