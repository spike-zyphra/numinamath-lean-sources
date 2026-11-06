import Mathlib

/- Problem 5
Prove that
$$
\left(a^{2}+2\right)\left(b^{2}+2\right)\left(c^{2}+2\right) \geq 9(a b+b c+c a)
$$
for all real numbers $a, b, c>0$. -/
theorem inequalities_209480 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a ^ 2 + 2) * (b ^ 2 + 2) * (c ^ 2 + 2) ≥ 9 * (a * b + b * c + c * a) := by
  nlinarith [sq_nonneg (a * b * c), sq_nonneg (a * b - 1), sq_nonneg (a * c - 1), sq_nonneg (b * c - 1),
    sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
