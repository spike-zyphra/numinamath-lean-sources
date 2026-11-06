import Mathlib

theorem algebra_272446 (l w : ℝ) (hl : l = 2) (hw : w = 1)
    (hle : l * w = 2) (hle' : l * w + 3 * (l + w) = 2 + 3 * (2 + 1)) :
    (2 * 1) * (1 + 2 / 100) = 2 := by 
  norm_num at hle hle' ⊢
  <;> linarith [hl, hw, hle, hle']