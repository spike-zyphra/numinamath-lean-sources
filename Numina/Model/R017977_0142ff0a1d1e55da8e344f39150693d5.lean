import Mathlib

def f_1125 : ℕ → ℕ
| 0 => 1
| 1 => 1
| n + 2 => f_1125 n + f_1125 (n + 1)

theorem number_theory_1125 : f_1125 2014 % 12 = 1 := by
  set_option maxRecDepth 10000 in 
  norm_num [f_1125]