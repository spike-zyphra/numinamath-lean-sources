import Mathlib

/- Example 9 Proof: For any $a, b, c>0$, we have
$$\frac{a}{b}+\frac{b}{c}+\frac{c}{a} \geqslant \frac{a+b}{b+c}+\frac{b+c}{a+b}+1$$-/
theorem inequalities_602768 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / b + b / c + c / a ≥ (a + b) / (b + c) + (b + c) / (a + b) + 1 := by
  -- It suffices to show that the left-hand side minus the right-hand side is greater than or equal to zero.
  have : a / b + b / c + c / a - (a + b) / (b + c) - (b + c) / (a + b) - 1 ≥ 0 := by
    calc
      _ = (a ^ 2 * c * (b + c) * (a + b) + a * b ^ 2 * (b + c) * (a + b) + b * c ^ 2 * (b + c) * (a + b) - a * b * c * (a + b) ^ 2 - a * b * c * (b + c) ^ 2 - a * b * c * (b + c) * (a + b)) / (a * b * c * (b + c) * (a + b)) := by
        -- Try to rewrite the expression with commonized denominator.
        field_simp [hb.ne', hc.ne', ha.ne', show b + c ≠ 0 by positivity, show a + b ≠ 0 by positivity]
        ring
      _ ≥ 0 := by
        -- We claim that numerator and denominator both non-negative.
        apply div_nonneg
        · -- Prove numerator ≥ 0.
          nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), show a * b > 0 by positivity, show b * c > 0 by positivity, show c * a > 0 by positivity]
        · -- Prove denominator > 0.
          positivity
  -- Close the goal using linarith.
  linarith