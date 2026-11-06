import Mathlib

theorem algebra_272969 (x y z : ℤ) :
    (x + y + z) ∣ x^3 + y^3 + z^3 - 3 * x * y * z := by 
  use x^2 + y^2 + z^2 - x * y - x * z - y * z 
  ring_nf