import Mathlib

def g : ℕ → ℕ
| 0 => 0
| n + 1 => g n + (Nat.digits 10 n).prod

theorem number_theory_7220 : g 8 ≤ 42273 := by 
  norm_num [g]