import Mathlib

theorem inequalities_74038 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 5 * a * b * c > a ^ 3 + b ^ 3 + c ^ 3) :
    a + b > c ∧ a + c > b ∧ b + c > a := by
  constructor
  · -- Assume $a + b \leq c$ leads to contradiction.
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
        sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a), 
        mul_pos (mul_pos ha hb) hc]
  constructor
  · -- Assume $a + c \leq b$ leads to contradiction.
    nlinarith [sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (c - a),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
        sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a), 
        mul_pos (mul_pos ha hb) hc]
  · -- Assume $b + c \leq a$ leads to contradiction.
    nlinarith [sq_nonneg (b - c), sq_nonneg (a - b), sq_nonneg (a - c),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
        sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a), 
        mul_pos (mul_pos ha hb) hc]