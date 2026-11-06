import Mathlib

theorem algebra_169443 {l w d : ℝ} (hl : l = 3) (hw : w = 2) (hd : d = 1.2)
    (h1 : 18 * l * w * d = 24 * l * w * (d - 0.4)) :
    24 * l * w * (d - 0.4) = 7.2 := by
  rw [hl, hw, hd] at h1 ⊢
  norm_num at h1 ⊢
  <;> linarith