import Mathlib

/- (a) Determine the minimal value of

$$
\left(x+\frac{1}{y}\right)\left(x+\frac{1}{y}-2018\right)+\left(y+\frac{1}{x}\right)\left(y+\frac{1}{x}-2018\right),
$$

where $x$ and $y$ vary over the positive reals.

(b) Determine the minimal value of

$$
\left(x+\frac{1}{y}\right)\left(x+\frac{1}{y}+2018\right)+\left(y+\frac{1}{x}\right)\left(y+\frac{1}{x}+2018\right),
$$

where $x$ and $y$ vary over the positive reals.

(Pierre Haas, Luxembourg)

#-/
theorem algebra_606349 :
    IsLeast {z | ∃ x y : ℝ, 0 < x ∧ 0 < y ∧ z = (x + 1 / y) * (x + 1 / y - 2018) + (y + 1 / x) * (y + 1 / x - 2018)} (-2036162) := by
  -- Simplify the goal into two parts.
  simp [IsLeast, lowerBounds, -one_div]
  refine ⟨?_, ?_⟩
  . -- Show that the minimum value is possible.
    let x := (1009 + Real.sqrt 1018077) / 2
    -- Show that x + 1 / x = 1009.
    have h : x + 1 / x = 1009 := by
      field_simp [show 0 < x by positivity, x]
      ring_nf
      field_simp
      ring_nf
    -- Use x = y.
    use x, by positivity, x, by positivity
    field_simp [show 0 < x by positivity, x]
    ring_nf
    field_simp [show Real.sqrt 1018077 ^ 4 = (Real.sqrt 1018077 ^ 2) ^ 2 by ring_nf]
    ring_nf
  . -- Show that the value is minimum.
    intro z x hx y hy hz
    rw [hz, <-ge_iff_le]
    -- Let a = x + 1 / x and b = y + 1 / y.
    let a := x + 1 / x
    let b := y + 1 / y
    -- Prove the inequality by series of calculations and estimations.
    calc
      _ = (x ^ 2 + 1 / x ^ 2) + (y ^ 2 + 1 / y ^ 2) + 2 * (x * (1 / y) + y * (1 / x)) - 2018 * (x + 1 / x + (y + 1 / y)) := by
        ring
      _ ≥ (x ^ 2 + 1 / x ^ 2) + (y ^ 2 + 1 / y ^ 2) + 2 * 2 - 2018 * (x + 1 / x + (y + 1 / y)) := by
        -- Use AM-GM inequality for the term x * (1 / y) + y * (1 / x).
        have : x * (1 / y) + y * (1 / x) ≥ 2 := by
          -- Change the inequality to x² + y² ≥ 2xy, which is equivalent to (x - y)² ≥ 0.
          field_simp
          rw [le_div_iff₀]
          linarith only [sq_nonneg (x - y)]
          positivity
        linarith only [this]
      _ = (a ^ 2 - 2) + (b ^ 2 - 2) + 4 - 2018 * (a + b) := by
        -- Write the inequality in terms of a and b.
        rw [show a ^ 2 = x ^ 2 + 1 / x ^ 2 + 2 by ring_nf; field_simp, show b ^ 2 = y ^ 2 + 1 / y ^ 2 + 2 by ring_nf; field_simp]
        ring
      _ = (a - 1009) ^ 2 + (b - 1009) ^ 2 - 2036162 := by
        -- Rewrite the expression.
        ring
      _ ≥ -2036162 := by
        -- Use the non-negativity of squares (a - 1009)² and (b - 1009)².
        linarith only [sq_nonneg (a - 1009), sq_nonneg (b - 1009)]
