import Mathlib

open Polynomial 

theorem algebra_16884 : (4 * (X + 5) * (X + 6) * (X + 10) * (X + 12) - 3 * X ^ 2 : Polynomial ℤ) =
    (2 * X ^ 2 + 35 * X + 120) * (X + 8) * (2 * X + 15) := by 
  ring_nf