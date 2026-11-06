import Mathlib

/-There is a sequence of numbers:
1,3,8,22,60,164,448,⋯ where the first number is 1, the second number is 3,
and starting from the third number, each number is exactly twice the sum of the previous two numbers.
In this sequence, the remainder when the 2000th number is divided by 9 is ?-/

def f (n : ℕ) : ℕ := match n with
| 0 => 5
| 1 => 1
| 2 => 3
| n + 3 => 2 * (f (n + 1) + f (n + 2))

theorem number_theory_170213: f 2000 % 9 = 3 := by
  set_option maxRecDepth 10000 in
  norm_num [f]