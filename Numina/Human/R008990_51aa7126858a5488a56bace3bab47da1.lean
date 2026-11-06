import Mathlib

/-
Randall proposes a new temperature system called Felsius temperature with the following conversion between Felsius ${ }^{\circ} E$, Celsius ${ }^{\circ} C$, and Fahrenheit ${ }^{\circ} F$ :

$$
{ }^{\circ} E=\frac{7 \times{ }^{\circ} C}{5}+16=\frac{7 \times{ }^{\circ} F-80}{9} .
$$

For example, $0^{\circ} C=16^{\circ} E$. Let $x, y, z$ be real numbers such that $x^{\circ} C=x^{\circ} E, y^{\circ} E=y^{\circ} F, z^{\circ} C=$ $z^{\circ} F$. Find $x+y+z$.
-/
theorem algebra_609814 {x y z : ℝ} (hx : x * (7 / 5) + 16 = x) (hy : (7 * y - 80) / 9 = y) (hz : z * (7 / 5) + 16 = (7 * z - 80) / 9) :  x + y + z = -120 := by
  -- Simplify equations based on given identities for specific equalities
  ring_nf at hx hy hz

  -- Use linarith to deduce the solution from simplified linear relationships

  have hx' : x = -40 := by linarith
  have hy' : y = -40 := by linarith
  have hz' : z = -40 := by linarith

  linarith