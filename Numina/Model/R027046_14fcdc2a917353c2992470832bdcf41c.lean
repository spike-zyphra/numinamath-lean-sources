import Mathlib

theorem algebra_252573 (l w h : ℝ) (hl : l = 75) (hw : w = 28) (hh : h = 40)
    (h1 : (l * w * (h - 25)) / (l * w * h) = 10 / 100) :
    (l * w * (h - 25)) / (l * w * h) = 9.135 := by 
  rw [hl, hw, hh] at h1 ⊢
  norm_num at h1 ⊢
  all_goals
    linarith