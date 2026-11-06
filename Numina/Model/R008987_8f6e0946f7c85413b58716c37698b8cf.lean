import Mathlib

theorem algebra_11587 {l w h : ℝ} (hl : l > 0) (hw : w > 0) (hw : h > 0)
    (hvol : l * w * h = 4320) (hsurf : 2 * (l * w + w * h + l * h) = 1704)
    (hedge : 4 * (l + w + h) = 208) :
    (l + 1) * (w + 1) * (h + 1) = 5225 := by
  have h1 : l * w + w * h + l * h = 852 := by
    linarith
  have h2 : l + w + h = 52 := by
    linarith
  have eq1 : (l + 1) * (w + 1) * (h + 1) = l * w * h + (l * w + w * h + l * h) + (l + w + h) + 1 := by
    ring
  rw [eq1]
  rw [show l * w * h = 4320 by linarith [hvol]]
  rw [show l * w + w * h + l * h = 852 by linarith [h1]]
  rw [show l + w + h = 52 by linarith [h2]]
  norm_num