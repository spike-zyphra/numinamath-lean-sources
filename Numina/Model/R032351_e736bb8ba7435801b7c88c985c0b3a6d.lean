import Mathlib

theorem inequalities_114746 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 / (1 + a ^ 2 * c) + 1 / (1 + b ^ 2 * c) = 1 ∧
    1 / (1 + a ^ 2 * b) + 1 / (1 + b ^ 2 * c) + 1 / (1 + c ^ 2 * a) < 2 := by
  constructor
  · -- Prove the equality $\frac{1}{1+a^{2}c}+\frac{1}{1 + b^2c}=1$
    have h1 : 0 < a ^ 2 * c := by
      positivity
    have h2 : 0 < b ^ 2 * c := by
      positivity
    field_simp
    nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a * c - 1), sq_nonneg (b * c - 1),
      habc, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]
  · -- Prove the inequality $\frac{1}{1+a^2b} + \frac{1}{1 + b^2c} + \frac{1}{1 + c^2a} < 2$
    have h12 : 0 < a ^ 2 * b := by
      positivity
    have h13 : 0 < b ^ 2 * c := by
      positivity
    have h14 : 0 < c ^ 2 * a := by
      positivity
    have h3 : 1 / (1 + a ^ 2 * b) + 1 / (1 + b ^ 2 * c) + 1 / (1 + c ^ 2 * a) - 2 < 0 := by
      have h12 : 0 < (1 + a ^ 2 * b) * (1 + b ^ 2 * c) * (1 + c ^ 2 * a) := by
        positivity
      have h13 : 1 / (1 + a ^ 2 * b) + 1 / (1 + b ^ 2 * c) + 1 / (1 + c ^ 2 * a) - 2 =
          ((1 + b ^ 2 * c) * (1 + c ^ 2 * a) + (1 + a ^ 2 * b) * (1 + c ^ 2 * a) + (1 + a ^ 2 * b) * (1 + b ^ 2 * c) - 2 * (1 + a ^ 2 * b) * (1 + b ^ 2 * c) * (1 + c ^ 2 * a)) / ((1 + a ^ 2 * b) * (1 + b ^ 2 * c) * (1 + c ^ 2 * a)) := by
        field_simp
        ring
      rw [h13]
      have h14 : (1 + b ^ 2 * c) * (1 + c ^ 2 * a) + (1 + a ^ 2 * b) * (1 + c ^ 2 * a) + (1 + a ^ 2 * b) * (1 + b ^ 2 * c) - 2 * (1 + a ^ 2 * b) * (1 + b ^ 2 * c) * (1 + c ^ 2 * a) < 0 := by
        nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          sq_nonneg (a * b * c - 1), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
          mul_pos (show 0 < a * b from mul_pos ha hb) hc
        ]
      have h15 : ((1 + b ^ 2 * c) * (1 + c ^ 2 * a) + (1 + a ^ 2 * b) * (1 + c ^ 2 * a) + (1 + a ^ 2 * b) * (1 + b ^ 2 * c) - 2 * (1 + a ^ 2 * b) * (1 + b ^ 2 * c) * (1 + c ^ 2 * a)) / ((1 + a ^ 2 * b) * (1 + b ^ 2 * c) * (1 + c ^ 2 * a)) < 0 := by
        apply div_neg_of_neg_of_pos
        linarith
        all_goals
          positivity
      linarith
    linarith