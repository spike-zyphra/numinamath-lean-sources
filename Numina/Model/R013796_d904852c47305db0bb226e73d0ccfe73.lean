import Mathlib

open Real

theorem algebra_289472 (x y : ℝ) :
    (x + y) % 1 ≤ x % 1 + y % 1 := by 
  norm_num [Nat.floor_le, Nat.lt_floor_add_one, add_assoc, Int.floor_add_int]
  all_goals try { omega }
  all_goals try { linarith }
  all_goals try { nlinarith }