import Mathlib

theorem algebra_9321 :IsLeast {x : ℤ | 6 - 3 * x < 0} 3 := by
  constructor
  · -- Show that 3 is in the set
    show 6 - 3 * (3 : ℤ) < 0
    norm_num
  · -- Show that 3 is the smallest element in the set
    intro y hy
    have h : 6 - 3 * y < 0 := by
      simpa using hy
    linarith