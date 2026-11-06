import Mathlib

/- Example 1.11.7. Let \(a, b, c\) be non-negative real numbers with sum 3. Prove that
$$\frac{a+b}{1+b}+\frac{b+c}{1+c}+\frac{c+a}{1+a} \geq 3$$ -/
theorem inequalities_602070 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hsum : a + b + c = 3) :
    3 ≤ (a + b) / (1 + b) + (b + c) / (1 + c) + (c + a) / (1 + a) := by
  -- Prove that denominators are positive
  have h1 : 1 + a > 0 := by linarith
  have h2 : 1 + b > 0 := by linarith
  have h3 : 1 + c > 0 := by linarith

  -- Reformulate the problem as showing that the difference with 3 is non-negative
  have h : (a + b) / (1 + b) + (b + c) / (1 + c) + (c + a) / (1 + a) - 3 ≥ 0 := by
    -- Express the difference as a single fraction
    have h4 : (a + b) / (1 + b) + (b + c) / (1 + c) + (c + a) / (1 + a) - 3 =
        ((a + b) * (1 + c) * (1 + a) + (b + c) * (1 + a) * (1 + b) + (c + a) * (1 + b) * (1 + c) - 3 * (1 + a) * (1 + b) * (1 + c)) /
        ((1 + a) * (1 + b) * (1 + c)) := by
      -- Simplify using field operations and ring properties
      field_simp
      ring

    -- Use the reformulated expression
    rw [h4]

    -- Prove that the fraction is non-negative
    apply div_nonneg
    -- Use non-linear arithmetic with various square non-negativity facts
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      hsum, mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc]
    -- Prove that the denominator is positive
    positivity

  -- Conclude the proof using linear arithmetic
  linarith
