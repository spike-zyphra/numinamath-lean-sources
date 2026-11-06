import Mathlib

theorem number_theory_236530 :
    (4275 / 45 : ℚ) < (3456 / 36 : ℚ) ∧
    (3456 / 36 : ℚ) < (4770 / 45 : ℚ) ∧
    (4770 / 45 : ℚ) < (3852 / 36 : ℚ) := by
  constructor
  · -- Show that 4275/45 < 3456/36
    norm_num
  constructor
  · -- Show that 3456/36 < 4770/45
    norm_num
  · -- Show that 4770/45 < 3852/36
    norm_num