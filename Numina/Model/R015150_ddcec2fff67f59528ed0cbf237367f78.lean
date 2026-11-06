import Mathlib

theorem algebra_238842 {x y z : ℝ} (h : x = (y + z) / 2) (h' : y = (x + z) / 3) (h'' : z = 10) :
    x + y + z = 24 := by
  rw [h''] at h h'
  linarith