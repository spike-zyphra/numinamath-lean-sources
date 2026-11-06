import Mathlib

theorem algebra_224796 {a b c d : ℝ} (h : a * c = 2 * b + 2 * d) :
    ∃ x, x ^ 2 + a * x + b = 0 ∨ x ^ 2 + c * x + d = 0 := by
  by_cases h1 : a ^ 2 - 4 * b ≥ 0
  · -- If $a^2 - 4b \geq 0$, then $x^2 + ax + b = 0$ has a root.
    use (-a + Real.sqrt (a ^ 2 - 4 * b)) / 2
    left
    have h2 : (Real.sqrt (a ^ 2 - 4 * b)) ^ 2 = a ^ 2 - 4 * b := by
      rw [Real.sq_sqrt]
      linarith
    nlinarith [Real.sqrt_nonneg (a ^ 2 - 4 * b), h2]
  · -- Assume h1 is false, so $a^2 - 4b < 0$, then we must have $c^2 - 4d \geq 0$
    have h2 : c ^ 2 - 4 * d ≥ 0 := by
      nlinarith [sq_nonneg (a - c), h]
    -- Now use the quadratic formula for $x^2 + c x + d = 0$
    use (-c + Real.sqrt (c ^ 2 - 4 * d)) / 2
    right
    have h3 : (Real.sqrt (c ^ 2 - 4 * d)) ^ 2 = c ^ 2 - 4 * d := by
      rw [Real.sq_sqrt]
      linarith
    nlinarith [Real.sqrt_nonneg (c ^ 2 - 4 * d), h3]