import Mathlib

def f (x : ℕ) := 3 * x + 2

theorem algebra_259924 : ∃ m, 0 < m ∧ 2005 ∣ f^[100] m := by
  use 380
  constructor
  · -- Show 380 > 0
    norm_num
  · -- Now need to prove 2005 divides f^[100](380)
    native_decide