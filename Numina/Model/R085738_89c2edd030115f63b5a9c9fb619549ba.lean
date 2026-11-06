import Mathlib

theorem inequalities_5327 : IsGreatest {x : ℤ | x ^ 2 - 24 * x - 83 ≤ 0} 27 := by
  constructor
  · -- Show 27 is in the set
    show (27 : ℤ) ^ 2 - 24 * (27 : ℤ) - 83 ≤ 0
    norm_num
  · -- Show for all x in the set, x ≤ 27
    intro x
    intro hx
    have h : x ^ 2 - 24 * x - 83 ≤ 0 := by
      simpa using hx
    nlinarith [sq_nonneg (x - 27 : ℤ)]