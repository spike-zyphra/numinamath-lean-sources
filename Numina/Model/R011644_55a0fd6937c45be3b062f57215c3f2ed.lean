import Mathlib

theorem inequalities_152271 (a b c d : ℝ) :
    (a + c) ^ 2 * (b + d) ^ 2 ≥ 2 * (a * b ^ 2 * c + b * c ^ 2 * d + c * d ^ 2 * a + d * a ^ 2 * b + 4 * a * b * c * d) ∧ (a + c) ^ 2 * (b + d) ^ 2 ≥ 4 * b * c * (c * d + d * a + a * b) := by
  constructor
  · -- Prove the first inequality
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * d), sq_nonneg (c * d - d * a), sq_nonneg (d * a - a * b),
              sq_nonneg (a * d - b * c), sq_nonneg (a * c - b * d), sq_nonneg (a - c), sq_nonneg (b - d),
              sq_nonneg (a * b + b * c + c * d + d * a), sq_nonneg (b * c - a * d)]
  · -- Prove the second inequality
    nlinarith [sq_nonneg (a * b - c * d), sq_nonneg (b * c - a * d), sq_nonneg (a * d - b * c), sq_nonneg (b * d - a * c),
              sq_nonneg ((a + c) * (b - d) - 2 * b * c), sq_nonneg ((a + c) * (d - b) + 2 * a * b),
              sq_nonneg ((a - c) * (b + d) + 2 * b * d), sq_nonneg ((c - a) * (b + d) - 2 * b * c),
              sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * d), sq_nonneg (c * d - d * a), sq_nonneg (d * a - a * b)
    ]