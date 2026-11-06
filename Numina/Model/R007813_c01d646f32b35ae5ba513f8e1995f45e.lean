import Mathlib

theorem algebra_13715 {l w : ℝ} (hl : l > 0) (hw : w > 0)
    (h : l * w = 432) (h1 : (l * 0.9) * (w * 1.1) = x) :
    round x = 428 := by
  have hx : x = 427.68 := by
    calc
      x = (l * 0.9) * (w * 1.1) := by rw [h1]
      _ = 0.9 * 1.1 * (l * w) := by ring
      _ = 0.9 * 1.1 * 432 := by rw [h]
      _ = 427.68 := by norm_num
  rw [hx]
  norm_num [round_eq]
  <;> norm_num