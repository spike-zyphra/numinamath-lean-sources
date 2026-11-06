import Mathlib
theorem inequalities_607359 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : b * c / (a ^ 2 + 2 * b * c) + c * a / (b ^ 2 + 2 * c * a) +
    a * b / (c ^ 2 + 2 * a * b) ≤ 1 ∧ 1 ≤ a ^ 2 / (a ^ 2 + 2 * b * c) + b ^ 2 / (b ^ 2 + 2 * c * a) + c ^ 2 / (c ^ 2 + 2 * a * b) := by 
  constructor
  · -- First part $\sum \frac{bc}{a^{2}+2bc} \le 1$
    have h1 : 0 < a ^ 2 + 2 * b * c := by
      nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    have h2 : 0 < b ^ 2 + 2 * c * a := by
      nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    have h3 : 0 < c ^ 2 + 2 * a * b := by
      nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    have h4 : b * c / (a ^ 2 + 2 * b * c) + c * a / (b ^ 2 + 2 * c * a) + a * b / (c ^ 2 + 2 * a * b) - 1 ≤ 0 := by
      have h5 : b * c / (a ^ 2 + 2 * b * c) + c * a / (b ^ 2 + 2 * c * a) + a * b / (c ^ 2 + 2 * a * b) - 1 =
          (b * c * (b^2 + 2 * c * a) * (c^2 + 2 * a * b) + c * a * (a^2 + 2 * b * c) * (c^2 + 2 * a * b) + a * b * (a^2 + 2 * b * c) * (b^2 + 2 * c * a) - (a^2 + 2 * b * c) * (b^2 + 2 * c * a) * (c^2 + 2 * a * b)) / ((a ^ 2 + 2 * b * c) * (b ^ 2 + 2 * c * a) * (c ^ 2 + 2 * a * b)) := by
        field_simp
        ring
      rw [h5]
      apply div_nonpos_of_nonpos_of_nonneg
      · -- To prove the first part $\sum \frac{bc}{a^{2}+2bc} \le 1$, we can rewrite it as $\sum \frac{bc}{a^{2}+2bc} - 1 \le 0$.
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
            sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
            sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
            mul_pos (show 0 < a ^ 2 by nlinarith) (show 0 < b ^ 2 by nlinarith),
            mul_pos (show 0 < a ^ 2 by nlinarith) (show 0 < c ^ 2 by nlinarith),
            mul_pos (show 0 < b ^ 2 by nlinarith) (show 0 < c ^ 2 by nlinarith)
          ]
      · -- Denominator is non-negative
        positivity
    linarith
  · -- Second part: $1 \le \sum \frac{a^2}{a^2 + 2bc}$ 
    have h1 : 0 < a ^ 2 + 2 * b * c := by
      nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    have h2 : 0 < b ^ 2 + 2 * c * a := by
      nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    have h3 : 0 < c ^ 2 + 2 * a * b := by
      nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    have h4 : a ^ 2 / (a ^ 2 + 2 * b * c) + b ^ 2 / (b ^ 2 + 2 * c * a) + c ^ 2 / (c ^ 2 + 2 * a * b) - 1 ≥ 0 := by
      have h5 : a ^ 2 / (a ^ 2 + 2 * b * c) + b ^ 2 / (b ^ 2 + 2 * c * a) + c ^ 2 / (c ^ 2 + 2 * a * b) - 1 =
          (a ^ 2 * (b^2 + 2 * c * a) * (c^2 + 2 * a * b) + b ^ 2 * (a^2 + 2 * b * c) * (c^2 + 2 * a * b) + c ^ 2 * (a^2 + 2 * b * c) * (b^2 + 2 * c * a) - (a^2 + 2 * b * c) * (b^2 + 2 * c * a) * (c^2 + 2 * a * b)) / ((a ^ 2 + 2 * b * c) * (b ^ 2 + 2 * c * a) * (c ^ 2 + 2 * a * b)) := by
        field_simp
        ring
      rw [h5]
      apply div_nonneg
      · -- To prove the second part $1 \le \sum \frac{a^2}{a^2 + 2bc}$, we can rewrite it as $\sum \frac{a^2}{a^2 + 2bc} - 1 \ge 0$.
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
            sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
            sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
            mul_pos (show 0 < a ^ 2 by nlinarith) (show 0 < b ^ 2 by nlinarith),
            mul_pos (show 0 < a ^ 2 by nlinarith) (show 0 < c ^ 2 by nlinarith),
            mul_pos (show 0 < b ^ 2 by nlinarith) (show 0 < c ^ 2 by nlinarith)
          ]
      · -- Denominator is non-negative
        positivity
    linarith