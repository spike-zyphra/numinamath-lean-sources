import Mathlib
open Real

/- What is the minimum value of the function $y= \frac {x^{2}+5}{ \sqrt {x^{2}+4}}$? -/
theorem algebra_9254 :
  IsLeast {y : ℝ | ∃ x, y = (x^2 + 5) / √(x^2 + 4)} (5 / 2) := by
  -- We have two goals to prove:
  -- 1. 5/2 can be achieved
  -- 2. (x^2 + 5) / √(x^2 + 4) ≥ 5/2 for all x
  simp [IsLeast, lowerBounds]
  constructor
  . -- Set x = 0 and simplify
    use 0
    simp [show √4 = √(2^2) by norm_num]
  . intro x
    -- Cancel the denominator
    rw [le_div_iff₀ (by positivity)]
    -- Square both sides
    suffices _ : (5 / 2 * √(x ^ 2 + 4))^2 ≤ (x^2 + 5)^2 by nlinarith
    -- Simplify the left-hand side
    ring_nf
    simp [show 4 + x^2 ≥ 0 by positivity]
    -- The goal is now to prove (4 + x ^ 2) * (25 / 4) ≤ 25 + x ^ 2 * 10 + x ^ 4
    -- This is equivalent to x^2 * (x^2 + 15/4) ≥ 0
    nlinarith [sq_nonneg x]
