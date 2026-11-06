import Mathlib

theorem inequalities_597970 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    4 * (a ^ 3 + b ^ 3) ≥ (a + b) ^ 3 ∧
    9 * (a ^ 3 + b ^ 3 + c ^ 3) ≥ (a + b + c) ^ 3 := by

  constructor
  · -- Prove the first inequality: $4(a^3 + b^3) \geq (a+b)^3$
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), mul_self_nonneg (a - b),
      mul_self_nonneg (a + b), ha.le, hb.le]

  · -- Prove the second inequality: $9(a^3 + b^3 + c^3) \geq (a+b+c)^3$
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a + b), sq_nonneg (b + c), sq_nonneg (c + a),
      mul_self_nonneg (a - b), mul_self_nonneg (b - c), mul_self_nonneg (c - a),
      mul_self_nonneg (a + b), mul_self_nonneg (b + c), mul_self_nonneg (c + a),
      ha.le, hb.le, hc.le]