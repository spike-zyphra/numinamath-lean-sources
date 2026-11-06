import Mathlib

/-Let $a, b$ and $c$ be positive reals such that $a + b + c \ge abc$. Prove that $a^2 + b^2 + c^2 \ge \sqrt3 abc$.-/

theorem inequalities_58034 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b * c ≤ a + b + c) :
    a ^ 2 + b ^ 2 + c ^ 2 ≥ Real.sqrt 3 * a * b * c := by 
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
    sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
    Real.sq_sqrt (show 0 ≤ 3 by norm_num),
    sq_nonneg (a - Real.sqrt 3), sq_nonneg (b - Real.sqrt 3), sq_nonneg (c - Real.sqrt 3),
    h]