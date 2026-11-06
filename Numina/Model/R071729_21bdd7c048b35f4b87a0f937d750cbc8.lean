import Mathlib

theorem algebra_195796 {x : ℝ} (hx : x ≠ 0) (h : (1 - 10 / 100) * x = 100) :
    x = 111 + 1 / 9 := by
  have h1 : (9 / 10) * x = 100 := by
    norm_num at h ⊢
    linarith
  have h2 : x = 100 * (10 / 9) := by
    linarith
  rw [h2]
  norm_num