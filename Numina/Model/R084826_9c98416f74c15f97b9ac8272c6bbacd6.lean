import Mathlib

theorem algebra_194676 (x y : ℝ) (hx : x > 0) (hy : y > 0)
    (h1 : x * 3.75 = y * 4.25) (h2 : x * 4.25 = y * 3.75 - 4) :
    x = 6 ∧ y = 6 := by
  have eq1 : x = 6 := by
    ring_nf at h1 h2 ⊢
    nlinarith [mul_pos hx hy]
  have eq2 : y = 6 := by
    ring_nf at h1 h2 ⊢
    nlinarith [mul_pos hx hy]
  constructor
  · linarith
  · linarith