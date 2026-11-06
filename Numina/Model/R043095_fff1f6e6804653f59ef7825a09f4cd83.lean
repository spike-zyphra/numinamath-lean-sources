import Mathlib

theorem inequalities_200055 :
    2^300 < 3^200 ∧ 2^40 < 3^28 ∧ 5^44 < 4^53 := by 
  constructor
  · -- Show that 2^300 < 3^200
    norm_num
  constructor
  · -- Show that 2^40 < 3^28
    norm_num
  · -- Show that 5^44 < 4^53
    norm_num