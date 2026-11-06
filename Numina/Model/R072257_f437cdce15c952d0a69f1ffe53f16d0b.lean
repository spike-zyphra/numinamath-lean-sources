import Mathlib

theorem algebra_130978 {x y z : ℤ} (h : x ≠ y ∧ y ≠ z ∧ z ≠ x) :
    5 * (x - y) * (y - z) * (z - x) ∣ (x - y)^5 + (y - z)^5 + (z - x)^5 := by
  use x^2 + y^2 + z^2 - x * y - y * z - z * x
  have hxy : x - y ≠ 0 := by intro h0; apply h.1; linarith
  have hyz : y - z ≠ 0 := by intro h0; apply h.2.1; linarith
  have hzx : z - x ≠ 0 := by intro h0; apply h.2.2; linarith
  ring_nf
  -- no further work needed as `ring_nf` proves equality
  -- need to verify by expansion
  <;> omega
  <;> nlinarith