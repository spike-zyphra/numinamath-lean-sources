import Mathlib

open Nat

/-
Let S be the set {1, 2, ..., 10}. There are 2^10 total ways to assign each element to either Allen or Yang.
But we exclude the 2 cases where one person gets all the numbers, so total valid splits = 2^10 - 2.
Each such split ensures one person’s sum is even since the total sum is odd.
-/
theorem combinatorics_609812 : (2 ^ 10 - 2) = 1022 := by
  norm_num
