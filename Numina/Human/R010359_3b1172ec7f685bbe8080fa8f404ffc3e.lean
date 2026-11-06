import Mathlib

open Polynomial

/-Use the Horner's method to calculate the value of the polynomial $f(x) = x^6 - 2x^5 + 3x^3 + 4x^2 - 6x + 5$ when $x = 2$.-/
theorem algebra_9335 {f : Polynomial ℤ} (hf : f = X^6 - 2*X^5 + 3*X^3 + 4*X^2 - 6*X + 5) :
  f.eval 2 = 33 := by
    -- Given the polynomial $f(x) = x^6 - 2x^5 + 3x^3 + 4x^2 - 6x + 5$, we can rewrite it using Horner's method as follows:
    -- $f(x) = x(x(x(x(x(x - 2) + 3) + 4) - 6) + 5$
    have _ : f = X * (X * (X * (X * (X * (X - 2) ) + 3) + 4) - 6)+ 5 := by
      rw [hf]; ring_nf
    simp [hf]
