import Mathlib

theorem inequalities_100798 (a b c d : ℝ) (h : a + b + c + d = 2) :
    ((a + b) ^ 2) / 2 ≤ a ^ 2 + b ^ 2 ∧ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≥ 1 := by
  constructor
  · -- Show that $\frac{(a+b)^{2}}{2} \leq a^{2}+b^{2}$ using $(a-b)^2 \geq 0$.
    nlinarith [sq_nonneg (a - b)]
  · -- Show that $a^{2}+b^{2}+c^{2}+d^{2} \geq 1$ using the constraint $a + b + c + d = 2$.
    nlinarith [sq_nonneg (a + b - 1), sq_nonneg (c + d - 1), sq_nonneg (a - b), sq_nonneg (c - d)]