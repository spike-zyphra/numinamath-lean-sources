import Mathlib

theorem inequalities_601928 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 1) :
    3 / 4 ≤ x ^ 3 / ((1 + y) * (1 + z)) + y ^ 3 / ((1 + z) * (1 + x)) +
    z ^ 3 / ((1 + x) * (1 + y)) := by
  -- Compute $\frac{3}{4}$ subtracted from the left side of the inequality
  have h1 : x ^ 3 / ((1 + y) * (1 + z)) + y ^ 3 / ((1 + z) * (1 + x)) + z ^ 3 / ((1 + x) * (1 + y)) - 3 / 4 ≥ 0 := by
    -- Convert the inequality to a no denominator version.
    -- Find common denominator (1 + x) * (1 + y) * (1 + z).
    -- Multiply both sides by it to clear denominators.
    have h2 : 0 < (1 + y) * (1 + z) * (1 + x) := by positivity
    have h3 : x ^ 3 / ((1 + y) * (1 + z)) + y ^ 3 / ((1 + z) * (1 + x)) + z ^ 3 / ((1 + x) * (1 + y)) - 3 / 4 =
        (x^3 * (1 + x) + y^3 * (1 + y) + z^3 * (1 + z) - 3 / 4 * ((1 + y) * (1 + z) * (1 + x)) ) / ((1 + y) * (1 + z) * (1 + x)) := by
      field_simp
      ring_nf
    rw [h3] at *
    apply div_nonneg
    -- Prove that the numerator is non-negative.
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
        hxyz, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
    ]
    all_goals
      positivity
  linarith