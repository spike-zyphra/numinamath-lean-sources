import Mathlib
/- Find all real solutions to $x^{4}+(2-x)^{4}=34$. -/
theorem algebra_611196 (x : ℝ) : x ^ 4 + (2 - x) ^ 4 = 34 ↔ x = 1 + √2 ∨ x = 1 - √2:= by
  constructor
  -- Forward direction: proving that if x^4 + (2-x)^4 = 34, then x = 1 ± √2
  .
    intro h
    -- Rewrite the equation into factored form
    replace h : ((x - 1) ^ 2 + 8) * ((x - 1) ^ 2 - 2) = 0:= by linarith
    -- Prove that (x-1)^2 + 8 cannot be zero (as it's always positive)
    have h1 : (x - 1) ^ 2 + 8 ≠ 0:= by positivity
    simp [h1] at h
    -- Factor (x-1)^2 - 2 into (x-1-√2)(x-1+√2)
    replace h1 : (x - 1 - √2) * (x - 1 + √2) = 0:= by
      ring_nf
      field_simp
      linarith
    simp at h1
    rcases h1 with h1 | h1
    -- Case 1: x = 1 + √2
    .
      left
      linarith
    -- Case 2: x = 1 - √2
    .
      right
      linarith
  -- Reverse direction: proving that if x = 1 ± √2, then x^4 + (2-x)^4 = 34
  .
    intro h
    rcases h with h | h
    -- Verify both cases by substitution and simplification
    all_goals
      subst x
      ring_nf
      rw [show √2 ^ 4 = √2 ^ 2 * √2 ^ 2 by ring]
      field_simp
      linarith
