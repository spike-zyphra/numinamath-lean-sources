import Mathlib

theorem algebra_4544 (P : Polynomial ℤ) (hP : P = 6*X^8 - 25*X^7 - 31*X^6 + 140*X^5 - 6*X^3 + 25*X^2 + 31*X - 140) :
    P = (X^5 - 1)*(X - 4)*(2*X - 5)*(3*X + 7) := by
  rw [hP]
  ring_nf