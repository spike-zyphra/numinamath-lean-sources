import Mathlib

open Real


/-
Given a function $f(x) = e^x + x^2 - x + \sin x$ defined on $\mathbb{R}$, find the equation of the tangent line to the curve $y = f(x)$ at the point $(0, f(0))$.
-/
theorem algebra_9033
    {f g : ℝ → ℝ}
    (hf : f = fun x => exp x + x ^ 2 - x + sin x)
    (a b : ℝ)
    (hg : g = fun x => a * x + b)
    (hg1 : deriv g 0 = deriv f 0)
    (hg2 : g 0 = f 0) :
    g = fun x => x + 1 := by

  -- Firstly, we compute the value of the function $f(x)$ at $x=0$:
  have r1 : f 0 = 1 := by simp [hf]

  -- Evaluating the derivative at $x=0$
  have r3 : deriv f 0 = 1 := by
    rw [hf, deriv_add, deriv_sub, deriv_add, deriv_pow, deriv_id'']
    any_goals simp [differentiableAt_exp, differentiableAt_sin]


  -- The slope of the tangent line at the point $(0, f(0))$ is equal to the derivative of $f(x)$ at that point, which we have found to be $1$.
  have ra : a = 1 := by
    rw [hg, deriv_add, deriv_mul, deriv_id'', deriv_const, r3] at hg1
    convert hg1
    any_goals simp
    apply DifferentiableAt.const_mul ?_ a
    exact differentiableAt_id'

  -- Given the slope $m = 1$ and the point $(0, 1)$, we have: $ y - 1 = 1 \cdot (x - 0). $
  have rb : b = 1 := by
    simp [hg, hf] at hg2
    exact hg2

  -- conclusion
  simp [hg, ra, rb]
