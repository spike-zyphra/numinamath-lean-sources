import Mathlib

theorem algebra_50822 {l w : ℝ} (hl : l > 0) (hw : w > 0)
    (h : l * w = 1100) (h1 : l * (1 + 10 / 100) * w * (1 - 10 / 100) = x) :
    x = 1089 := by
  have h2 : l * (1 + 10 / 100) * w * (1 - 10 / 100) = 0.99 * (l * w) := by
    ring_nf
  rw [h2] at h1
  rw [h] at h1
  norm_num at h1 ⊢
  linarith