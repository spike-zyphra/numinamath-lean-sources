import Mathlib

theorem algebra_883 (h : (1 / 2 + 1 / 5 + 1 / 8 + 1 / 11 + 1 / 20 + 1 / 41 + 1 / 110 + 1 / 1640) = 1) :
    -1 / 2 - 1 / 5 - 1 / 8 + 1 / 11 - 1 / 20 - 1 / 41 + 1 / 110 + 1 / 1640 = -131 / 164 := by 
  norm_num at h ⊢
  all_goals linarith