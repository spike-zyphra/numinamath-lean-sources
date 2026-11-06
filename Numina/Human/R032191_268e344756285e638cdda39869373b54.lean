import Mathlib

/- Given that the solution set of the quadratic inequality $x^{2}-ax-a \leqslant -3$ with respect to $x$ is not empty, find the range of values for the real number $a$ . -/
theorem algebra_9082 (a : ℝ) :
    (∃ x : ℝ, x^2 - a * x - a ≤ -3) ↔ a ≤ -6 ∨ a ≥ 2 := by
  -- The minimum value of x^2 - ax - a is attained at x = a/2
  constructor <;> intro h
  . obtain ⟨x, h⟩ := h
    -- -3 ≥ x ^ 2 - a * x - a ≥ (a/2) ^ 2 - a * (a/2) - a
    -- Thus nlinarith with (x-a/2) ^ 2 ≥ 0 can solve the problem
    by_contra!
    nlinarith [sq_nonneg (x - a / 2)]
  . -- Set x = a/2
    use a / 2
    contrapose! h
    constructor <;> nlinarith
