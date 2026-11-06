import Mathlib

def f (n : ℕ) := match n % 7 with
  | 0 => 1
  | 1 => 2
  | 2 => 5
  | 3 => 10
  | 4 => 25
  | 5 => 50
  | 6 => 100
  | _ => 0

theorem number_theory_278028 : f 17 + f 74 = 35 := by
  simp [f]
  all_goals omega