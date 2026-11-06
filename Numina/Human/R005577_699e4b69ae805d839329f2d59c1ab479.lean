import Mathlib
open Polynomial
/- Find the sum of the coefficients of the polynomial $P(x)=x^{4}-29 x^{3}+a x^{2}+b x+c$, given that $P(5)=11, P(11)=17$, and $P(17)=23$. -/
theorem algebra_608941 (P : ℝ[X]) (a b c : ℝ) (h : P = X ^ 4 - 29 * X ^ 3 + Polynomial.C a * X ^ 2 + Polynomial.C b * X + Polynomial.C c) (h1 : Polynomial.eval 5 P = 11) (h2 : Polynomial.eval 11 P = 17) (h3 : Polynomial.eval 17 P = 23) : Polynomial.eval 1 P = -3193:= by
  -- Substitute the polynomial definition into the goal
  subst P
  -- Simplify the evaluation conditions
  simp at h1 h2 h3
  -- Simplify the goal
  simp
  -- Solve the linear system of equations
  linarith
