import Mathlib

open Polynomial

/- The equation $x^2 + 2x - 2 = 0$ is transformed into the form $(x + m)^2 = 3$. Find the value of $m$.-/
theorem algebra_9145 {p q : ℝ[X]} {m : ℝ} (hp : p = X ^ 2  + C 2 * X - C 2)
    (hq : q = (X + C m) ^ 2 - 3) (hpq : p = q) : m = 1 := by
  -- We know that two polynomials are equal if and only if there coefficients are the same.
  -- Given polynomials p(x)=x^2-2x-2 and q(x)=(x+m)^2-3.
  rw [Polynomial.ext_iff, hp, hq, show (X + C m) ^ 2 = X ^ 2 + 2 * C m * X + C m ^ 2 by ring] at hpq
  -- We compare their linear coefficients.
  specialize hpq 1
  -- Which gives 2 = 2m.
  simp at hpq
  rw [show C m ^ 2 = C (m ^ 2) from Eq.symm C_pow, coeff_C_succ] at hpq
  -- Hence, we deduce that m=1.
  linarith
