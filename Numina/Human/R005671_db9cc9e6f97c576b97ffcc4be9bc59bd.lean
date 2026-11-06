import Mathlib

/-
This theorem calculates the probability that exactly 1000 people end up in jail when the game ends, given an initial setup of 1001 townspeople and 2 goons.
-/
theorem Combinatorics_609347:
    ∏ k in Finset.range 500, 
    ((1001 - 2 * (k : ℕ)) : ℝ) / (1003 - 2 * (k : ℕ))
    = (3 : ℝ) / 1003 := by

  norm_num