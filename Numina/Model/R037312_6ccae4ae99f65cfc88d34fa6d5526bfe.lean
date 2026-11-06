import Mathlib

open Polynomial
theorem algebra_285233 {R : Type*} [CommRing R] : 
  (Polynomial.X^2 + Polynomial.X + 1 : Polynomial R) * 
  (Polynomial.X^8 - Polynomial.X^7 + Polynomial.X^5 - Polynomial.X^4 + Polynomial.X^3 - Polynomial.X + (1 : Polynomial R)) = 
  Polynomial.X^10 + Polynomial.X^5 + (1 : Polynomial R) := by
  ring_nf