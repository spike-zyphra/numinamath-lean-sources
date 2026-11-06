import Mathlib
open Polynomial

theorem algebra_1465
    {a b c m : ℚ}
    (h1 : a + 2 * b + 3 * c = m)
    (h2 : a + b + 2 * c = m) :
    b = -c := by
  linarith