import Mathlib
/- Find the real solutions of $(2 x+1)(3 x+1)(5 x+1)(30 x+1)=10$. -/
theorem algebra_610847 (x : ℝ) : (2 * x + 1) * (3 * x + 1) * (5 * x + 1) * (30 * x + 1) = 10 ↔ x = (-4 + √31) / 15 ∨ x = (-4 - √31) / 15:= by
  constructor
  -- Forward direction: if equation holds, then x equals one of the two solutions
  .
    intro h
    -- Simplify the equation to a quadratic form
    replace h : (15 * x ^ 2 + 8 * x - 1) * (15 * x ^ 2 + 8 * x + 9 / 4) = 0:= by linarith
    -- Prove that the second factor is always positive
    have h1 : 15 * x ^ 2 + 8 * x + 9 / 4 > 0:= by
      have h1 : (x + 4 / 15) ^ 2 ≥ 0:= by positivity
      linarith
    -- Therefore the second factor cannot be zero
    replace h1 : 15 * x ^ 2 + 8 * x + 9 / 4 ≠ 0:= by linarith
    simp [h1] at h
    -- Express the equation in terms of the two solutions
    replace h : (x - (-4 + √31) / 15) * (x - (-4 - √31) / 15) = 0:= by
      ring_nf
      field_simp
      linarith
    simp at h
    rcases h with h | h
    -- Handle first solution
    .
      left
      linarith
    -- Handle second solution
    .
      right
      linarith
  -- Backward direction: if x equals either solution, then the equation holds
  .
    intro h
    rcases h with h | h
    -- Verify both solutions satisfy the original equation
    all_goals
      subst x
      ring_nf
      field_simp
      rw [show √31 ^ 4 = √31 ^ 2 * √31 ^ 2 by ring]
      field_simp
      linarith
