import Mathlib

/- Let $a, b, c > 0$ such that $a + b + c \leq 1$. Prove that \[\frac{a}{1 - a} + \frac{b}{1 - b} + \frac{c}{1 - c} \geq \frac{3(a + b + c)}{3 - (a + b + c)}.\]-/
theorem inequalities_618378 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≤ 1) :
    a / (1 - a) + b / (1 - b) + c / (1 - c) ≥ 3 * (a + b + c) / (3 - (a + b + c)) := by
  -- Show that the denominators 1 - a, 1 - b, 1 - c, 3 - (a + b + c) are positive.
  have h1 : 1 - a > 0 := by linarith
  have h2 : 1 - b > 0 := by linarith
  have h3 : 1 - c > 0 := by linarith
  have h4 : 3 - (a + b + c) > 0 := by linarith
  have h5 : a / (1 - a) + b / (1 - b) + c / (1 - c) - 3 * (a + b + c) / (3 - (a + b + c)) ≥ 0 := by
    calc
      _ = (a * (1 - b) * (1 - c) * (3 - (a + b + c)) + b * (1 - a) * (1 - c) * (3 - (a + b + c)) + c * (1 - a) * (1 - b) * (3 - (a + b + c)) - 3 * (a + b + c) * (1 - a) * (1 - b) * (1 - c)) / ((1 - a) * (1 - b) * (1 - c) * (3 - (a + b + c))) := by
        -- Use field_simp to simplify the expression to a common denominator.
        field_simp
        ring
      _ ≥ 0 := by
        apply div_nonneg
        . -- We use (a - b)² ≥ 0, (b - c)² ≥ 0 and (a + b + c - 1)² ≥ 0 to show that the numerator is non-negative.
          nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a + b + c - 1)]
        . -- The denominator is clearly positive.
          positivity
  exact le_of_sub_nonneg h5