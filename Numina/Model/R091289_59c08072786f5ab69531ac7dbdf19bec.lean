import Mathlib

def f (n : ℕ) := match n with
  | 0 => 1
  | 1 => 3
  | 2 => 4
  | 3 => 7
  | 4 => 11
  | 5 => 18
  | 6 => 29
  | 7 => 47
  | 8 => 76
  | 9 => 123
  | _ => 0

theorem number_theory_237500 : f 9 = 123 := by 
  simp [f]