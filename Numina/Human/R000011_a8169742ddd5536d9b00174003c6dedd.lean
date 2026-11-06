import Mathlib

/- Solve the following system of equations:
$$
x y = x + 2 y, \quad y z = y + 3 z, \quad z x = z + 4 x.
$$-/
theorem algebra_4023 {x y z : ℚ} (hy : y-1≠0) (hy' : y-3≠0) (h1 : x*y=x+2*y) (h2 : y*z=y+3*z) (h3 : z*x=z+4*x) :
    (x=0 ∧ y=0 ∧ z=0) ∨ (x=25/9 ∧ y=25/7 ∧ z=25/4) := by
  -- xy - x = 2y \implies x(y - 1) = 2y
  have hxy : x*y-x*1=2*y := by rw [← sub_eq_zero, ← sub_eq_zero_of_eq h1]; ring
  -- \implies x = \frac{2y}{y-1}
  rw [← mul_sub, ← eq_div_iff hy] at hxy
  --  yz - 3z = y \implies z(y - 3) = y
  have hxz : z*y-z*3=y := by rw [← sub_eq_zero, ← sub_eq_zero_of_eq h2]; ring
  --  \implies z = \frac{y}{y-3}
  rw [← mul_sub, ← eq_div_iff hy'] at hxz
  -- Substitute \(x = \frac{2y}{y-1}\) and \(z = \frac{y}{y-3}\) into the third equation \(zx = z + 4x\):
  --  \[
  --  \left( \frac{y}{y-3} \right) \left( \frac{2y}{y-1} \right) = \frac{y}{y-3} + 4 \left( \frac{2y}{y-1} \right)
  --  \]
  rw [hxy, hxz] at h3
  -- Simplify the left-hand side and right-hand side:
  --  \[
  --  \frac{2y^2}{(y-3)(y-1)} = \frac{y}{y-3} + \frac{8y}{y-1}
  --  \]
  field_simp at h3
  -- Remove the denominators by multiplying every term by \((y-3)(y-1)\):
  --  \[
  --  2y^2 = y(y-1) + 8y(y-3)
  --  \]
  ring_nf at h3
  -- Factor the equation:
  --  \[
  --  y(7y - 25) = 0
  --  \]
  have : y*(7*y-25)=0 := by rw [show (0 : ℚ)=-0 by ring, ← sub_eq_zero_of_eq h3]; ring
  -- Solve for \(y\):
  --  \[
  --  y = 0 \quad \text{or} \quad y = \frac{25}{7}
  --  \]
  rw [mul_eq_zero] at this
  rcases this with h | h
  -- If \(y = 0\):
  --    \[
  --    x = \frac{2 \cdot 0}{0-1} = 0, \quad z = \frac{0}{0-3} = 0
  --    \]
  . simp [h] at *; left; exact ⟨h1.symm, h2⟩
  -- If \(y = \frac{25}{7}\):
  --    \[
  --    x = \frac{2 \left( \frac{25}{7} \right)}{\frac{25}{7} - 1} = \frac{2 \left( \frac{25}{7} \right)}{\frac{18}{7}} = \frac{50}{18} = \frac{25}{9}
  --    \]
  --    \[
  --    z = \frac{\frac{25}{7}}{\frac{25}{7} - 3} = \frac{\frac{25}{7}}{\frac{4}{7}} = \frac{25}{4}
  --    \]
  rw [sub_eq_zero, mul_comm, ← eq_div_iff (by norm_num)] at h
  simp [h] at *
  rw [hxy, hxz]
  constructor <;> norm_num
