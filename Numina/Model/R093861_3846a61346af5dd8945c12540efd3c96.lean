import Mathlib

def f (n : ℕ) : ℕ := match n with
| 0 => 1
| 1 => 1
| n + 2 => f n + f (n + 1)

theorem number_theory_212289 : f 7 = 21 := by
  rfl