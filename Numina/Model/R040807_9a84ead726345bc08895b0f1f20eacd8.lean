import Mathlib

open Nat

theorem algebra_20979 : √(7!) = 12 * √35 := by
  calc
    √(7!) = √5040 := by
      norm_num [Nat.factorial]
    _ = √(12^2 * 35) := by
      norm_num
    _ = (12 : ℝ) * √35 := by
      rw [Real.sqrt_mul (by norm_num)]
      rw [Real.sqrt_sq (by norm_num)]
      all_goals norm_num
    _ = 12 * √35 := by
      ring