import Mathlib

open Real Set

theorem algebra_15948 :
    IsLeast {t : ℝ | ∃ x y, t = x ^ 2 + 2 * x * y + 3 * y ^ 2 - 6 * x - 2 * y} (-11) := by
  constructor
  · -- Show -11 is in the set
    use 4, -1
    norm_num
  · -- Show -11 is the least in the set
    intro t ht
    rcases ht with ⟨x, y, ht⟩
    nlinarith [sq_nonneg (x - 4), sq_nonneg (y + 1), sq_nonneg (x + y - 3), sq_nonneg (x - 4 + 2 * (y + 1)), sq_nonneg (2 * (x - 4) - (y + 1))]