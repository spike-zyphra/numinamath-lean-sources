import Mathlib
theorem algebra_305870 (a b : ℝ) (h : a^2 + a * b + b^2 = 1) :
    1 / 3 ≤ a^2 - a * b + b^2 ∧ a^2 - a * b + b^2 ≤ 3 := by 
  -- We know $a^2 + b^2 = 1 - a \cdot b$.
  have h1 : a^2 + b^2 = 1 - a * b := by
    linarith
  -- Show $ab \leq \frac{1}{3}$.
  have h2 : a * b ≤ (1 / 3) := by 
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
  -- Show $ab \geq -1$.
  have h3 : a * b ≥ -1 := by 
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
  -- Use the bounds on $ab$ to find bounds on $a^2 - a \cdot b + b^2$
  -- Since $a^2 - a \cdot b + b^2 = 1 - 2ab$, we can find its bounds.
  constructor
  · -- Prove lower bound
    nlinarith [h, h2, h3]
  · -- Prove upper bound
    nlinarith [h, h2, h3]