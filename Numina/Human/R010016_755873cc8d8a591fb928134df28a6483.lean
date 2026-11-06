import Mathlib

/-Compute the sum of the geometric series $-1 + 2 - 4 + 8 - \cdots + 512$.-/
theorem algebra_12777 : ∑ i ∈ Finset.range 10, (-1 : ℤ) ^ (i + 1) * 2 ^ i = 341 := by
-- Since there are not so many terms, a straighforward "norm_num" will finish the goal
norm_num