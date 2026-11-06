import Mathlib

open Real

theorem algebra_105822 (x y : ℝ) :
    (x + y) % 1 ≤ x % 1 + y % 1 := by
  norm_num [Nat.floor_le]
  <;> try { linarith [Int.floor_le (x : ℝ), Int.floor_le (y : ℝ), Int.floor_le (x + y : ℝ), Int.le_floor_add x y] }