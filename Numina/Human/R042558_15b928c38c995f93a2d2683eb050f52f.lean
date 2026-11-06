import Mathlib

/- Russian 1998 Problem 3 Can you find positive integers a, b, c, so that the sum of any two has digit sum less than 5, but the sum of all three has digit sum more than 50? -/
theorem number_theory_144389 : ∃ (a b c : ℕ), 0 < a ∧ 0 < b ∧ 0 < c ∧
    (Nat.digits 10 (a + b)).sum < 5 ∧ (Nat.digits 10 (a + c)).sum < 5 ∧
    (Nat.digits 10 (b + c)).sum < 5 ∧ (Nat.digits 10 (a + b + c)).sum > 50 := by
  -- Give an explicit construction satisfying the conditions of the problem
  use 4554554555
  use 5455455455
  use 5545545545
  -- Simp is able to clear the goals, which just use basic addition
  simp