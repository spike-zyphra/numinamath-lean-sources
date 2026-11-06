import Mathlib

theorem inequalities_597089 (a b c : ℝ) :
    4*(a^4+b^4+c^4)+3*(a^3*b+b^3*c+c^3*a) ≥
    7/27*(a+b+c)^4 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2),
          sq_nonneg (a^2 - a * b), sq_nonneg (b^2 - b * c), sq_nonneg (c^2 - c * a), 
          sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2),
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b)
]