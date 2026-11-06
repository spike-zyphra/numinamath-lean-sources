import Mathlib

def lucas (n : ℕ) : ℕ := match n with
| 0 => 1
| 1 => 3
| n + 2 => lucas n + lucas (n + 1)

theorem number_theory_15203 : lucas 99 % 8 = 7 := by
  norm_num [lucas]