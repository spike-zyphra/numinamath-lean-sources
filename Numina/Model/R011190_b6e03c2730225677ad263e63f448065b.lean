import Mathlib

def f (n : ℕ) : ℕ := match n with
| 0 => 2
| 1 => 3
| n + 2 => (f n) * (f (n + 1)) % 10

theorem number_theorem_229705: f 2016 = 2 := by
  set_option maxRecDepth 10000 in
  norm_num [f]