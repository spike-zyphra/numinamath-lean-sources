import Mathlib

def f (n : ℕ) : ℕ := match n with
| 0 => 1
| 1 => 9
| 2 => 9
| n + 3 => (f n + f (n + 1) + f (n + 2)) % 3

theorem number_theory_771 : f 1998 = 0 := by
  set_option maxRecDepth 10000 in
  simp [f]