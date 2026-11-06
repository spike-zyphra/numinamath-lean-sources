import Mathlib

theorem algebra_206233 {x y z : ℤ} (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x) :
    5 * (x - y) * (y - z) * (z - x) ∣ (x - y)^5 + (y - z)^5 + (z - x)^5 := by
  use x^2 + y^2 + z^2 - x * y - y * z - z * x
  ring_nf