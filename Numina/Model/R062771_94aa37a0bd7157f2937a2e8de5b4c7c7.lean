import Mathlib

theorem algebra_281909 {l w : ℝ} (hl : l > 0) (hw : w > 0)
    (h1 : w = (2 / 3) * l) (h2 : 2 * (l + w) = 148) :
    w * l = 1314.24 := by
  have h3 : l + w = 74 := by
    linarith

  rw [h1] at h3

  have hl_val : l = 74 * (3 / 5) := by
    linarith

  have hw_val_simp : w = 74 * (2 / 5) := by
    rw [h1, hl_val]
    ring

  rw [hw_val_simp, hl_val]
  norm_num