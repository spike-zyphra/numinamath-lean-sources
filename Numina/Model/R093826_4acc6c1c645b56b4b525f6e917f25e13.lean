import Mathlib

def fib (n : ℕ) : ℕ := match n with
| 0 => 1
| 1 => 1
| n + 2 => fib n + fib (n + 1)

theorem number_theory_19004 : fib 99 % 4 = 3 := by
  norm_num [fib]