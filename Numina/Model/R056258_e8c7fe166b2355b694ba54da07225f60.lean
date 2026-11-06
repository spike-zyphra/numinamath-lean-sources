import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_176115 (f : ℝ → ℝ) (hf : f = λ x => (x + 1) * (x + 2) * (x + 3) * (x + 4) + 35) :
    IsLeast (range f) 34 := by
  constructor
  · -- Show that 34 is attained at some specific value of x
    -- A quadratic about (x^2 +5x +5) and square_root
    -- Let's find the roots of $x^2 +5x +5 =0$ which are $x = (-5) / 2 ± √5 /2$
    use (-5 / 2 + Real.sqrt 5 / 2)
    simp [hf]
    -- Need to work with the expressions in Solid, so we compute the product (x + 1)(x + 2)(x + 3)(x + 4) at x = (-5 / 2 + sqrt 5 / 2) and add 35
    -- Expand to quadratic in sqrt 5^2 = 5 from Real.sq_sqrt
    nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num), sq_nonneg ((-5 / 2 + Real.sqrt 5 / 2) ^ 2 + 5 * (-5 / 2 + Real.sqrt 5 / 2) + 5)]
    -- The computed expression simplifies to y^2 where y is the value due to Real.sq_sqrt yielding equality
  · -- Show that 34 is a lower bound
    intro y hy
    rcases hy with ⟨x, hx⟩
    simp [hf] at hx
    -- Simplify the expression, we can do the same process as in the previous part
    -- square of a term is non-negative, so the whole expression is at least -35 +35=0, but here we can directly bound to show it is 34
    nlinarith [sq_nonneg (x ^ 2 + 5 * x + 5), sq_nonneg (x ^ 2 + 2 * x), sq_nonneg (x + 1/2), sq_nonneg (x + 5/2), sq_nonneg (x * (x + 5)), sq_nonneg (x + 2), sq_nonneg (x + 3), Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num), sq_nonneg ((-5 / 2 + Real.sqrt 5 / 2) ^ 2 + 5 * (-5 / 2 + Real.sqrt 5 / 2) + 5)]