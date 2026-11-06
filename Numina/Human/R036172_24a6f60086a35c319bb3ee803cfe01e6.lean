import Mathlib

/- Let $x$ be a real number. Find the maximum value of $2^{x(1-x)}$. -/
theorem algebra_608744 : IsGreatest { r | ∃ x : ℝ, r = (2:ℝ) ^ (x * (1 - x))} (2 ^ ((1:ℝ) / 4)) := by
  unfold IsGreatest upperBounds
  simp
  constructor
  -- when x = 1/2, 2^(x(1-x)) = 2^(1/4)
  . use 1/2
    ring_nf
  . intro x
    -- transform x(1-x) to (x-1/2)^2 - 1/4
    rw [show x * (1 - x) = -(x-1/2)^2 + 1/4 by ring]
    -- square always non-negative
    apply le_of_sub_nonneg
    simp
    exact sq_nonneg _
