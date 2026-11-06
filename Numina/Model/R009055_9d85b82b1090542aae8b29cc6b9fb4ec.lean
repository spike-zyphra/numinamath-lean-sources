import Mathlib

theorem algebra_15781 :
    IsGreatest {x : ℤ | 5 - 4 * x > 17} (-4) := by 
  constructor
  · -- Show that -4 is indeed in the set, so that 5 - 4*(-4) > 17.
    show 5 - 4 * (-4 : ℤ) > 17
    norm_num
  · -- Show that for any integer x in the set, x <= -4.
    intro x
    intro hx
    have h1 : 5 - 4 * (x : ℤ) > 17 := by 
      simpa using hx
    linarith