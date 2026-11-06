import Mathlib

open Real

lemma lemma_1 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
  a * b + b * c + c * a + a * b * c * (a + b + c) ≥ 6 * a * b * c := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc]

theorem inequalities_89689 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (a - b * c) ^ 2 + (b - c * a) ^ 2 + (c - a * b) ^ 2 ≥
    1 / 2 * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
        sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc,
        mul_nonneg (mul_nonneg ha hb) hc]