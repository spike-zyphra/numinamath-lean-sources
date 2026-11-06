import Mathlib

theorem inequalities_600807
    (a b c : ℝ)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hc : 0 ≤ c) :
    a^4 + b^4 + c^4 - 2*(a^2*b^2+b^2*c^2+c^2*a^2) +
    a^2*b*c+b^2*c*a+c^2*a*b ≥ 0 := by
  nlinarith [sq_nonneg (a - b + c), sq_nonneg (a + b - c), sq_nonneg (-a + b + c), sq_nonneg (a - b - c),
          sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc,
          mul_nonneg (mul_nonneg ha hb) hc
]