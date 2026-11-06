import Mathlib

theorem algebra_95141 {l w : ℝ} (hl : l > 0) (hw : w > 0)
    (h1 : (l + 2.5) * (w - 2 / 3) = l * w) (h2 : (l - 2.5) * (w + 4 / 3) = l * w) :
    l * w = 20 := by
  ring_nf at h1 h2
  nlinarith [sq_nonneg (l - 15 / 2), sq_nonneg (w - 8 / 3), mul_pos hl hw]