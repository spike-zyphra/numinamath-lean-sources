import Mathlib

theorem inequalities_2641 : (-1998 / 1999 : ℝ) < (-1997 / 1998 : ℝ) ∧ (-1997 / 1998 : ℝ) < (-98 / 99 : ℝ) ∧ (-98 / 99 : ℝ) < (-97 / 98 : ℝ) := by
  constructor
  · -- Show that -1998/1999 < -1997/1998
    norm_num
  constructor
  · -- Show that -1997/1998 < -98/99
    norm_num
  · -- Show that -98/99 < -97/98
    norm_num