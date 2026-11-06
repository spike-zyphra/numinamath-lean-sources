import Mathlib

def f (n : ℕ) : ℕ := match n with
  | 0 => 2001
  | 1 => 2002
  | 2 => 2003
  | n + 3 => f n + f (n + 1) - f (n + 2)

theorem algebra_18801 : f 2003 = 0 := by
  set_option maxRecDepth 20000 in 
  norm_num [f]
  <;> omega