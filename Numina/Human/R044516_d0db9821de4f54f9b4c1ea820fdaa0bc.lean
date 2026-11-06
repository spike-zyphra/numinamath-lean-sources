import Mathlib
/- Find the minimum of $x^{2}-2 x$ over all real numbers $x$. -/
theorem algebra_608398 : IsLeast {a : ℝ | ∃ x : ℝ, a = x ^ 2 - 2 * x} (-1):= by
  -- Split the proof into two parts: showing -1 is in the set and it's a lower bound
  constructor
  -- First part: prove that -1 belongs to the set
  .
    simp
    -- Use x = 1 to show that -1 is achievable
    use 1
    ring
  -- Second part: prove that -1 is a lower bound
  .
    simp [lowerBounds]
    intro x
    -- Use the fact that (x-1)^2 ≥ 0 to complete the proof
    suffices (x - 1) ^ 2 ≥ 0 by linarith
    positivity
