import Mathlib

def a : ℕ → ℤ
| 0 => 2000
| 1 => 2007
| n + 2 => a (n + 1) - a n

theorem algebra_179071 : a 2006 = 7 := by
  set_option maxRecDepth 10000 in
  norm_num [a]