import Mathlib
open Real Set
open scoped Real

/- Find the minimum value of the function $y=\cos^2x-3\cos x+2$. -/
theorem algebra_9403 : IsLeast {x | ∃ t : ℝ, x = cos t ^ 2 - 3 * cos t + 2} 0 := by
  -- Expand the definitions and split the goals.
  simp [IsLeast, lowerBounds]
  refine ⟨?_, ?_⟩
  . use 0 -- The minimum can be attained when t = 0.
    rw [cos_zero]
    linarith
  . intro t -- For any t, cos t ≤ 1, so (cos t - 1) * (cos t - 2) ≥ 0.
    have : 0 ≤ (cos t - 1) * (cos t - 2) := by
      nlinarith [cos_le_one t]
    linarith
