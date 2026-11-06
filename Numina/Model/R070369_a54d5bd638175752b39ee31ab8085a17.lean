import Mathlib

theorem algebra_10490 : IsGreatest {n | (n^2 - 9 * n + 18 : ℤ) < 0} 5 := by
  constructor
  · -- Show that 5 is in the set
    norm_num
  · -- Show that 5 is greatest: if n is in the set, then n ≤ 5.
    intro n hn
    have h : (n : ℤ) ^ 2 - 9 * (n : ℤ) + 18 < 0 := by
      simpa using hn
    have h1 : n ^ 2 - 9 * n + 18 < 0 := by
      exact_mod_cast h
    have h3 : n < 6 := by
      nlinarith
    have h4 : n > 0 := by
      nlinarith [h1]
      -- Now need to prove n ≤ 5
      -- $n < 6 \Rightarrow n \leq 5$
    have h5 : n ≤ 5 := by
      omega
    linarith