import Mathlib

theorem algebra_20042 : IsGreatest {x : ℝ | (4 * x + 11) * (2 * x - 8) = x * (2 * x + 7)} (11 / 2) := by 
  constructor
  · -- Show that 11/2 is indeed in the set.
    norm_num
  · -- Show that any x in the set is less than or equal to 11/2
    intro x
    intro hx
    have h : (4 * x + 11) * (2 * x - 8) = x * (2 * x + 7) := by 
      simpa using hx
    have h1 : 6 * x ^ 2 - 17 * x - 88 = 0 := by
      nlinarith 
    nlinarith [sq_nonneg (x - 11 / 2)]