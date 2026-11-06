import Mathlib
/- 5*. Positive numbers $a, b$ and $c$ are such that $a b c=1$. Prove the inequality

$$
\frac{1}{1+a+b}+\frac{1}{1+b+c}+\frac{1}{1+c+a} \leqslant 1
$$ -/
theorem inequalities_280602 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 / (1 + a + b) + 1 / (1 + b + c) + 1 / (1 + c + a) ≤ 1 := by
  -- Prove that the product of denominators is positive
  have h4 : (1 + a + b) * (1 + b + c) * (1 + c + a) > 0 := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  -- Multiply both sides of the inequality by the product of denominators
  -- This is valid because we're multiplying by a positive number
  suffices (1 / (1 + a + b) + 1 / (1 + b + c) + 1 / (1 + c + a)) * ((1 + a + b) * (1 + b + c) * (1 + c + a)) ≤ 1 * ((1 + a + b) * (1 + b + c) * (1 + c + a)) by
    apply (mul_le_mul_iff_of_pos_right h4).mp
    linarith
  -- Simplify the left side of the inequality
  -- After multiplying by the product of denominators, each fraction term becomes a product of two denominators
  have h5 : (1 / (1 + a + b) + 1 / (1 + b + c) + 1 / (1 + c + a)) * ((1 + a + b) * (1 + b + c) * (1 + c + a)) =
            (1 + b + c) * (1 + c + a) + (1 + c + a) * (1 + a + b) + (1 + a + b) * (1 + b + c) := by
    field_simp
    linarith
  rw [h5]
  -- Use nonlinear arithmetic to prove the inequality
  -- We provide several useful facts: squares are nonnegative, products of positive numbers are positive,
  -- and our constraint that a*b*c = 1
  nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
    sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, habc]
