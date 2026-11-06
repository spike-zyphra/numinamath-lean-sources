import Mathlib
/- Find all ordered pairs $(x, y)$ such that

$$
(x-2 y)^{2}+(y-1)^{2}=0
$$ -/
theorem algebra_608404 (x y : ℝ) : (x - 2 * y) ^ 2 + (y - 1) ^ 2 = 0 ↔ x = 2 ∧ y = 1:= by
  -- Split into forward and backward directions
  constructor
  -- Forward direction: if (x - 2y)² + (y - 1)² = 0, then x = 2 and y = 1
  .
    intro h
    -- Both squared terms are non-negative
    have h1 : (x - 2 * y) ^ 2 ≥ 0:= by positivity
    have h2 : (y - 1) ^ 2 ≥ 0:= by positivity
    -- Since sum is 0 and both terms are non-negative, both must be 0
    replace h1 : (x - 2 * y) ^ 2 = 0:= by linarith
    replace h2 : (y - 1) ^ 2 = 0:= by linarith
    -- Simplify squared terms equal to 0
    simp at h1 h2
    constructor
    -- Solve the system of equations
    all_goals
      linarith
  -- Backward direction: if x = 2 and y = 1, then (x - 2y)² + (y - 1)² = 0
  .
    intro h
    -- Destructure the conjunction
    rcases h with ⟨h1, h2⟩
    -- Substitute x = 2 and y = 1
    subst x y
    -- Simplify the expression
    ring_nf
