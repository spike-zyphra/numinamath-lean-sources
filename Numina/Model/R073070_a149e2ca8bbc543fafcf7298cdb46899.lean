import Mathlib

theorem algebra_199046 (r b : ℝ) (hr : r > 0) (hb : b > 0)
    (h : b = 1.25 * r) (h1 : 124 / r = 96 / b) :
    r = 82 := by
  rw [h] at h1
  field_simp at h1 ⊢
  nlinarith