import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_229459 : IsLeast {z : ℝ | ∃ x y, z = (4 * x ^ 2 + 2 * y ^ 2 - 4 * y + 4) / (2 * x ^ 2 + y ^ 2 - 2 * y + 5)} (1 / 2) := by 
  constructor
  · -- Show that 1/2 is indeed in the set, using x = 0 and y = 1
    use 0
    use 1
    norm_num 
  · -- Show that 1/2 is a lower bound for all values in the set
    intro z h
    rcases h with ⟨x, y, hz⟩
    have h1 : (4 * x ^ 2 + 2 * y ^ 2 - 4 * y + 4) / (2 * x ^ 2 + y ^ 2 - 2 * y + 5) ≥ (1 / 2 : ℝ) := by 
      have pos1 : (2 * x ^ 2 + y ^ 2 - 2 * y + 5) > 0 := by
        nlinarith [sq_nonneg (x), sq_nonneg (y - 1)]
      apply (le_div_iff₀ pos1).mpr 
      nlinarith [sq_nonneg (x), sq_nonneg (y - 1)]
    linarith [hz, h1]