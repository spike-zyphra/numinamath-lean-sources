import Mathlib

theorem algebra_1118
  (a b c : ℝ) (hmeana: (a + b + c) / 3 = a + 10) (hmeanc: (a + b + c) / 3 = c - 15) (hmedian: b = 5)
  : a + b + c = 30 := by
    rw [hmedian] at hmeana hmeanc 
    linarith