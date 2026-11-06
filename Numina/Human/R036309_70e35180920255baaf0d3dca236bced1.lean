import Mathlib

/- Example 1.10.10. Let $a, b, c$ be non-negative real numbers. Prove that
$$2\left(a^{3}+b^{3}+c^{3}\right)+a b c+a b+b c+c a+2 \geq 2\left(a^{2} b+b^{2} c+c^{2} a\right)+a^{2}+b^{2}+c^{2}+a+b+c$$-/
theorem inequalities_601765 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    2 * (a ^ 3 + b ^ 3 + c ^ 3) + a * b * c + a * b + b * c + c * a + 2 ≥
    2 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) + a ^ 2 + b ^ 2 + c ^ 2 + a + b + c := by
  -- Inspired by the equality case a = b = c = 1, we try to use (a - b)² ≥ 0, (b - c)² ≥ 0, (c - a)² ≥ 0, (a - 1)² ≥ 0, (b - 1)² ≥ 0 and (c - 1)² ≥ 0 and the non-negativity of a, b and c to accomplish the proof.
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc]