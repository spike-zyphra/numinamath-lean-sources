import Mathlib

theorem algebra_9101
    {a : ℕ → ℝ}
    (ha₀ : a 1 = 4)
    (hsum : ∀ n, ∑ i in Finset.range (n + 1), a i - 3 * ∑ i in Finset.range n, a i - 2 * n - 4 = 0)
    : ∀ n, a n = 5 * 3 ^ (n - 1) - 1 := by
  -- First apply the recurrence to n = 0
  have h1 := hsum 0
  -- Then apply the recurrence to n = 1
  have h2 := hsum 1
  -- Expanding the sums
  -- For n = 0, the first sum is from range 1 which is [a0]
  -- The second sum is from range 0 which is empty, sum is 0
  -- Therefore, equation reduces to a0 =4
  -- For n =1, the first sum is from range 2 which is [a0, a1]
  -- The second sum is from range 1 which is [a0]
  -- Therefore, (a0 + a1) - 3*(a0) - 2 - 4 = 0
  -- Expanding: a0 + a1 - 3a0 - 6 = 0
  -- Simplifying: -2a0 + a1 - 6 = 0
  -- From which -2a0 + a1 = 6
  -- We know a1 =4 from ha0
  -- So: -2a0 + 4 = 6
  -- Therefore -2a0 = 2
  -- So a0 = -1
  -- But from h1, we derived that a0 =4
  -- This is contradictory, so the theorem statement is vacuously true since the premises are inconsistent
  norm_num [Finset.sum_range_succ, ha₀] at h1 h2
  all_goals linarith