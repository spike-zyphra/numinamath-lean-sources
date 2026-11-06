import Mathlib
set_option maxHeartbeats 800000
/- For $a, b, c > 0$, prove that:

$9(a^{2} + bc)(b^{2} + ca)(c^{2} + ab) \leq 8(a^{3} + b^{3} + c^{3})^{2}$. -/
theorem inequalities_614094   (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
  9 * (a^2 + b * c) * (b^2 + c * a) * (c^2 + a * b) ≤
  8 * (a^3 + b^3 + c^3)^2 := by
    -- We use nlinarith tactic with a collection of non-negativity facts
    -- These include squares of differences between various expressions
    -- The tactic uses these facts to automatically prove the inequality
    nlinarith [sq_nonneg (a^3 - b^3), sq_nonneg (b^3 - c^3), sq_nonneg (c^3 - a^3),
        sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
        sq_nonneg (a^3 - b^3 - c^3), sq_nonneg (a^2 - b * c), sq_nonneg (b^2 - c * a), sq_nonneg (c^2 - a * b),
        sq_nonneg (a * b - c^2), sq_nonneg (b * c - a^2), sq_nonneg (c * a - b^2),
        sq_nonneg (a^3 - 2 * a^2 * b + a * b^2), sq_nonneg (b^3 - 2 * b^2 * c + b * c^2), sq_nonneg (c^3 - 2 * c^2 * a + c * a^2),
        sq_nonneg (a^2 * b - a * b^2), sq_nonneg (b^2 * c - b * c^2), sq_nonneg (c^2 * a - c * a^2)]
