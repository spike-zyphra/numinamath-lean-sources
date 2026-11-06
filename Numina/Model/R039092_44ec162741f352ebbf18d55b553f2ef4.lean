import Mathlib

def f (n : ℕ) : ℕ := match n with
| 0 => 130
| 1 => if Even (f 0) then f 0 / 2 + 2 else f 0 * 2 - 2
| 2 => if Even (f 1) then f 1 / 2 + 2 else f 1 * 2 - 2
| 3 => if Even (f 2) then f 2 / 2 + 2 else f 2 * 2 - 2
| n + 4 => if Even (f (n + 3)) then f (n + 3) / 2 + 2 else f (n + 3) * 2 - 2

theorem number_theory_125274 : f 2015 = 6 := by
  set_option maxRecDepth 10000 in
  native_decide