import Mathlib


theorem algebra_21740 : IsLeast {n | n ^ 2 - 5 * n - 14 < 0} (-1) := by
  constructor
  · -- We need to show that -1 is indeed in the set
    norm_num
  · -- We need to show that for any n in the set, -1 ≤ n
    intro n hn
    have h : n ^ 2 - 5 * n - 14 < 0 := by
      simpa using hn
    nlinarith