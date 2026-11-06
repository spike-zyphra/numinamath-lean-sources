import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_267490 (x y : ℝ)
  (h₁ : x + 2 * y ≥ 2) (h₂ : 2 * x + y ≤ 4) (h₃ : 4 * x - y ≥ 1) :
  19 / 9 ≤ 3 * x + y ∧ 3 * x + y ≤ 6 := by
  constructor
  · -- To prove that $19/9 \leq 3x + y$, let's find coefficients $\alpha, \beta, \gamma$ such that $\alpha(x + 2y) + \beta(2x + y) + \gamma(4x - y) \geq 19/9$.
    linarith
  · -- To prove that $3x + y \leq 6$, let's find coefficients $\alpha, \beta, \gamma$ such that $\alpha(x + 2y) + \beta(2x + y) + \gamma(4x - y) \leq 6$.
    linarith