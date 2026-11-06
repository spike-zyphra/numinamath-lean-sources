import Mathlib

theorem algebra_15382 : IsGreatest {x : ℤ | 5 - 4 * x > 17 } (-4) := by
  constructor
  · -- Show that -4 is indeed in the set {x : ℤ | 5 - 4 * x > 17 }
    show 5 - 4 * (-4) > 17
    norm_num
  · -- Now we need to show that -4 is greatest in the set
    intro x
    intro hx
    have h : 5 - 4 * x > 17 := hx
    linarith