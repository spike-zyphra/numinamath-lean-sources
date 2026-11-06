import Mathlib
set_option maxHeartbeats 800000
/- Example 8.2.1. Let \(a, b, c\) be positive real numbers with sum 2. Prove that
\[a^{2} b^{2} + b^{2} c^{2} + c^{2} a^{2} + a b c \leq 1\]
(Pham Kim Hung) -/
theorem inequalities_601031 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsum : a + b + c = 2) :
    a^2 * b^2 + b^2 * c^2 + c^2 * a^2 + a * b * c ≤ 1 := by
  -- Express c in terms of a and b using the sum constraint
  have h1 : c = 2 - a - b := by linarith
  -- Substitute the expression for c into the inequality
  rw [h1]
  -- Use nonlinear arithmetic to prove the inequality
  -- We provide several useful facts to help the solver:
  -- 1. Squares of differences are non-negative
  -- 2. Products of positive numbers are positive
  -- 3. Squares of various expressions are non-negative
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - (2 - a - b)), sq_nonneg (b - (2 - a - b)),
    mul_pos ha hb, mul_pos hb (show 0 < (2 - a - b) by nlinarith), mul_pos ha (show 0 < (2 - a - b) by nlinarith),
    sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg ((2 - a - b) - 1),
    sq_nonneg (a + b - 2), sq_nonneg (a - b), sq_nonneg (a - (2 - a - b)), sq_nonneg (b - (2 - a - b))]
