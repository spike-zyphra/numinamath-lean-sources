import Mathlib

theorem algebra_263787 {l w : ℚ} (hl : l = 3 / 5) (hw : l * w = 1 / 3) :
    w = 5 / 9 := by 
  rw [hl] at hw 
  have hw2 : (3 / 5 : ℚ) * w = 1 / 3 := hw
  have hw3 : w = (1 / 3) * (5 / 3 : ℚ) := by
    field_simp at hw2 ⊢
    linarith 
  norm_num at hw3 
  linarith