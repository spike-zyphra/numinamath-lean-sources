import Mathlib
set_option maxHeartbeats 800000
/- Example 1.1.12. Let \(a, b, c\) be non-negative real numbers with sum 2. Prove that
\[a^{2} b^{2} + b^{2} c^{2} + c^{2} a^{2} \leq 2\] -/
theorem inequalities_600816 (a b c : ℝ)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hc : 0 ≤ c)
    (hsum : a + b + c = 2) :
    a^2 * b^2 + b^2 * c^2 + c^2 * a^2 ≤ 2 := by

  -- Express c in terms of a and b using the sum condition
  have h1 : c = 2 - a - b := by linarith

  -- Substitute the expression for c into the inequality
  rw [h1]

  -- Use nlinarith to solve the inequality with various non-negativity conditions
  -- These include square non-negativity facts and various product non-negativity facts
  -- The key inequalities needed for the proof are provided to the solver
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a - b),
            sq_nonneg (a + b - 2), sq_nonneg (a - 1), sq_nonneg (b - 1),
            mul_nonneg ha hb, mul_nonneg hb (show 0 ≤ 2 - a - b by nlinarith),
            mul_nonneg ha (show 0 ≤ 2 - a - b by nlinarith),
            sq_nonneg (a^2 * b^2 + b^2 * (2 - a - b)^2 + (2 - a - b)^2 * a^2 - 2),
            sq_nonneg (a * b - 1), sq_nonneg (b * (2 - a - b) - 1), sq_nonneg (a * (2 - a - b) - 1)]
