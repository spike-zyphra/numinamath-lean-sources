import Mathlib

def f (n : ℕ) : ℕ := match n with
  | 0 => 20
  | 1 => if Even (f 0) then (f 0) / 2 else 3 * (f 0) + 1
  | 2 => if Even (f 1) then (f 1) / 2 else 3 * (f 1) + 1
  | 3 => if Even (f 2) then (f 2) / 2 else 3 * (f 2) + 1
  | n + 4 => if Even (f (n + 3)) then (f (n + 3)) / 2 else 3 * (f (n + 3)) + 1

theorem number_theory_264322 : f 9 = 2 := by 
  norm_num [f, Nat.even_iff]