import Mathlib

theorem inequalities_597214 (a b c : ℝ) :
    (a^2 + a * b + b^2) * (b^2 + b * c + c^2) * (c^2 + c * a + a^2) ≥
    3 * (a^2 * b + b^2 * c + c^2 * a) * (a * b^2 + b * c^2 + c * a^2) := by
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
            sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)),
            sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
            sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            mul_nonneg (show (0 : ℝ) ≤ (a - b) ^ 2 by nlinarith) (show (0 : ℝ) ≤ (b - c) ^ 2 by nlinarith),
            mul_nonneg (show (0 : ℝ) ≤ (a - b) ^ 2 by nlinarith) (show (0 : ℝ) ≤ (c - a) ^ 2 by nlinarith),
            mul_nonneg (show (0 : ℝ) ≤ (b - c) ^ 2 by nlinarith) (show (0 : ℝ) ≤ (c - a) ^ 2 by nlinarith)
]