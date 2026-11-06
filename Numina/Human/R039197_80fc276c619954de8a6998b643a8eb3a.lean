import Mathlib

/-
3. Let $x, y$ be positive reals such that $x+y=2$. Prove that


$$

x^{3} y^{3}\left(x^{3}+y^{3}\right) \leq 2

$$

 -/
theorem inequalities_125994 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 2) :
    x^3 * y^3 * (x^3 + y^3) ≤ 2 := by
  -- first rewrite the lhs as 2(xy)^3(2^2 - 3xy), the two 2's are coming from x + y
  convert_to 2 * (x * y)^3 * (2^2  - 3  * (x * y)) ≤ 2
  . rw [← hxy]
    ring
  -- set z = xy to and show proving 0 ≤ (z - 1)^2*(3z^2 + 2z + 1) is enough
  set z := x*y with hz
  suffices 0 ≤ (z - 1)^2 * (3 * z ^2 + 2 * z + 1) by
    linarith
  -- rewrite the quadratic as square + positive, so rhs is positive obviously
  rw [show 3 * z ^2 + 2 * z + 1 = 3 * (z + 1/3)^2 + 2 / 3 by ring]
  positivity