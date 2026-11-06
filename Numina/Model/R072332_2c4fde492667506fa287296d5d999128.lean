import Mathlib

theorem algebra_21756 (x : ℤ) (hx : (x - 5) * (x + 5) < 0) :
    IsLeast {x | (x - 5) * (x + 5) < 0} (-4) := by
  constructor
  · -- Show that -4 is in the set
    norm_num
  · -- Show that any integer y in the set is ≥ -4
    intro y hy
    have h1 : (y - 5) * (y + 5) < 0 := by
      simpa using hy
    have : y ≥ -4 := by
      nlinarith
    linarith