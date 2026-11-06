import Mathlib

theorem algebra_1596 {x : ℝ} (hx : 0 < x) (h : (100 + x) * 0.2 = 100 * 0.3333 + x) :
    x = 25 := by
  norm_num at h ⊢
  linarith