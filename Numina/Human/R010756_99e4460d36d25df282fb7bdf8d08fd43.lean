import Mathlib

open Polynomial

/- What is the coefficient of $x^2$ when $-5x^3 - 5x^2 - 7x + 1$ is multiplied by $-x^2 - 6x + 1$ and the like terms are combined? -/
theorem algebra_15603 {p q: ℤ[X]} (hp: p = -5*X^3-5*X^2-7*X+1)
  (hq: q = -X^2-6*X+1): (p * q).coeff 2 = 36 := by
  -- calculate the product. in fact, coefficient of x^2 can only come from constant mul x^2 and x mul x, we only care about these terms.
  have h1: p * q = (5*X^5 + 35*X^4 + 32*X^3 - 13*X + 1) + 36*X^2 :=
  calc
    p*q = (-5*X^3-5*X^2-7*X+1) * (-X^2-6*X+1) := by rw [hp,hq]
    _ = ((-5*X^3-5*X^2-7*X)*(-X^2)-X^2) +
        ((-5*X^3-5*X^2+1)*(-6*X)-7*X*(-6*X))+
        (-5*X^3-7*X+1) -5*X^2 := by ring
    _ = (-5*X^3-5*X^2-7*X)*(-X^2) + (-5*X^3-5*X^2+1)*(-6*X) +
        (-5*X^3-7*X+1) + (-X^2+42*X^2-5*X^2) := by ring
    _ = (5*X^5+5*X^4+7*X^3) + (30*X^4+30*X^3-6*X) +
        (-5*X^3-7*X+1) + 36*X^2 := by ring
      -- in fact, only the last term counts, -1+42-5=36 is the answer.
    _ = 5*X^5 + 35*X^4 + 32*X^3 - 13*X + 1 + 36*X^2 := by ring
    _ = (5*X^5 + 35*X^4 + 32*X^3 - 13*X + 1) + 36*X^2 := by ring
  -- obviously, coefficient of X^2 is 36.
  rw [h1, coeff_add _ _ 2]
  simp [coeff_one, coeff_X]