import Mathlib


/-
What is the sum of the $x$-values that satisfy the equation $5=\frac{x^3-2x^2-8x}{x+2}$?
-/
theorem algebra_10961 :
    {x : ℝ | 5 = (x ^ 3 - 2 * x ^ 2 - 8 * x) / (x + 2)} = {-1, 5} ∧
    -1 + 5 = 4 := by
  constructor

  -- We can factor $x$ out of the numerator so that we're left with $$\frac{x(x^2-2x-8)}{x+2}=\frac{x(x-4)(x+2)}{x+2}$$
  . ext x
    by_cases h : x + 2 = 0
    . simp [eq_neg_of_add_eq_zero_left h]
      norm_num
    . -- After canceling out the $x+2$ from the numerator and denominator, we have $x(x-4)=5$.
      have : (x ^ 3 - 2 * x ^ 2 - 8 * x) / (x + 2) = x * (x - 4) := by
        rw [show x ^ 3 - 2 * x ^ 2 - 8 * x = x * (x - 4) * (x + 2) by ring]
        rw [mul_div_cancel_right₀]
        exact h
      simp [this]
      -- Solving for the roots of a quadratic equation, we have $x^2-4x-5=0$, which gives us $(x-5)(x+1)=0$ and $x=5$ or $x=-1$.
      have : 5 = x * (x - 4) ↔ (x - 5) * (x + 1) = 0 := by
        constructor
        all_goals intro; ring_nf; linarith
      simp only [this, mul_eq_zero, sub_eq_zero, eq_neg_iff_add_eq_zero.symm, or_comm]
  -- The sum of these values is $\boxed{4}$, which is our answer.
  . norm_num
