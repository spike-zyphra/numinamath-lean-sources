import Mathlib

open Real Set

theorem algebra_21468 :
    IsLeast {z : ℝ | ∃ x y, z = 2 * x ^ 2 + 2 * x * y + 4 * y + 5 * y ^ 2 - x} (-5 / 4) := by 
  constructor 
  · -- Show that -5/4 is in the set.
    use 1 / 2, -1 / 2
    norm_num 
  · -- Show that -5/4 is the least element in the set.
    intro z h 
    rcases h with ⟨x, y, hz⟩
    nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (y + 1 / 2),
              sq_nonneg (2 * x + y - 1), sq_nonneg (4 * y + 2), sq_nonneg (x + y), sq_nonneg (x - y)]