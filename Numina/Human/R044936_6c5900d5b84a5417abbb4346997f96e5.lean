import Mathlib
set_option maxHeartbeats 800000
/- Example 3 For any positive real numbers $a, b, c$, prove:
$$\left(a^{2}+2\right)\left(b^{2}+2\right)\left(c^{2}+2\right) \geqslant 9(a b+b c+c a)$$ -/
theorem inequalities_602078 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a ^ 2 + 2) * (b ^ 2 + 2) * (c ^ 2 + 2) ≥ 9 * (a * b + b * c + c * a) := by
  -- Using nlinarith tactic with several non-negative expressions to help the solver
  -- These include squares of various expressions which are always non-negative
  -- For example: (a*b*c)², (a*b-1)², (a-b)², etc.
  nlinarith [sq_nonneg (a * b * c), sq_nonneg (a * b - 1), sq_nonneg (a * c - 1), sq_nonneg (b * c - 1),
    sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
