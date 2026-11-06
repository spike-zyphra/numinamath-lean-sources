import Mathlib

def a (n : ℕ) : ℤ := match n with
  | 0 => 1
  | 1 => 3
  | n + 2 => abs (a (n + 1)) - a n

theorem algebra_10952 : ∑ i in Finset.range 100, a i = 89 := by
  norm_num [Finset.sum_range_succ, a]