import Mathlib

open Nat

theorem algebra_10767 : √((8 !) / 70 : ℝ) = 24 := by 
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num [Nat.factorial]