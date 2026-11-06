import Mathlib
open Real Set

/- The maximum value of the function $y=\sin 2x + 2\cos x - 3$ is ______. -/
theorem algebra_8988 : IsGreatest {x | ∃ t : ℝ, x = sin (2 * t) + 2 * cos t - 3} (3 * √3 /2 - 3) := by

  -- Split into two goals:
  -- 1. The value can be achieved
  -- 2. The value is an upper bound
  constructor <;> simp [upperBounds]

  . -- Set x = π / 6 and simplify
    use π / 6
    simp [(by linarith : 2 * (π / 6) = π / 3)]
    linarith

  . intro x
    -- Square the both sides
    refine le_of_abs_le (abs_le_of_sq_le_sq ?_ (by positivity))

    -- Rewrite sin(2x) = 2sin(x)cos(x), cos^2(x) = 1 - sin^2(x) and simplify
    rw [sin_two_mul]
    ring_nf; simp
    rw [cos_sq']

    -- Let sin x = t, and the inequality is equivalent to:
    -- (2t - 1)^2 * ((2t + 3)^2 + 2) ≥ 0
    generalize sin x = t
    have : (2 * t - 1) ^2 * ((2 * t + 3) ^ 2 + 2) ≥ 0 := by positivity
    linarith
