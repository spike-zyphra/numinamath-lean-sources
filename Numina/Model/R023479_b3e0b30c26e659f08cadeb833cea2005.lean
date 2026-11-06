import Mathlib

theorem algebra_322612 (a : ℤ) (h : ∃ x y z, x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
    2*x^3-3*a*x^2+2*(a+7)*x+a^2-9*a+8=0 ∧
    2*y^3-3*a*y^2+2*(a+7)*y+a^2-9*a+8=0 ∧
    2*z^3-3*a*z^2+2*(a+7)*z+a^2-9*a+8=0 ∧
    x=1 ∧ y=2 ∧ z=3) :
    a=4 := by
  rcases h with ⟨x, y, z, hxy, hyz, hzx, hx, hy, hz, hx1, hy2, hz3⟩
  rw [hx1] at hx
  rw [hy2] at hy
  rw [hz3] at hz
  have eq1 := hx
  have eq2 := hy
  have eq3 := hz
  ring_nf at eq1 eq2 eq3
  nlinarith