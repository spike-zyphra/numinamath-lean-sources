import Mathlib

/- Given real positive numbers $a, b, c$ and $d$, for which the equalities $a^2 + ab + b^2 = 3c^2$ and $a^3 + a^2b + ab^2 + b^3 = 4d^3$ are fulfilled. Prove that $$a + b + d \le 3c.$$ -/
theorem inequalities_37223 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h1 : a^2 + a * b + b^2 = 3 * c^2) (h2 : a^3 + a^2 * b + a * b^2 + b^3 = 4 * d^3) :
    a + b + d ≤ 3 * c := by
  -- The proof uses nlinarith (nonlinear arithmetic) tactic with several facts:
  -- 1. (a - b)² ≥ 0 - a basic square is nonnegative
  -- 2. (a + b - 2*c)² ≥ 0 - another square is nonnegative
  -- 3. (d - c)² ≥ 0 - another square is nonnegative
  -- 4. The given equations h1 and h2
  -- 5. Various positivity facts derived from the hypotheses
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 2 * c), sq_nonneg (d - c),
    h1, h2, mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd]
