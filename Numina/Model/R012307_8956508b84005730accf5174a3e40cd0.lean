import Mathlib
import Mathlib.Order.Basic
import Mathlib.Data.Set.Defs
open Set

theorem algebra_20533 : IsLeast {n : ℤ | 5 * n + 3 > -10} (-2) := by
  constructor
  · -- Show that -2 is in the set
    norm_num
  · -- Show that if n is in the set, then n ≥ -2
    intro n hn
    have h : 5 * n + 3 > -10 := by
      simpa using hn
    omega