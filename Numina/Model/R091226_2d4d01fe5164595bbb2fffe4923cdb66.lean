import Mathlib

theorem algebra_6181 :
    IsGreatest {x + y | (x : ℕ) (y : ℕ) (hx : 0 < x) (hy : 0 < y)
      (h : 13 * x + 5 * y = 262)} 46 := by
  constructor
  · -- Show that the value 46 is indeed achievable
    exact ⟨4, 42, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · -- Show that no value greater than 46 is achievable
    intro n hn
    rcases hn with ⟨x, y, hx, hy, h, hxy⟩
    omega