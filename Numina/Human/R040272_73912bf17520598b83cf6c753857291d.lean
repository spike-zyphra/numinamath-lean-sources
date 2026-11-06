import Mathlib

/- Find all positive reals $x,y,z $ such that \[2x-2y+\dfrac1z = \dfrac1{2014},\hspace{0.5em} 2y-2z +\dfrac1x = \dfrac1{2014},\hspace{0.5em}\text{and}\hspace{0.5em} 2z-2x+ \dfrac1y = \dfrac1{2014}.\] -/
theorem algebra_75705 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : 2 * x - 2 * y + 1 / z = 1 / 2014) (h2 : 2 * y - 2 * z + 1 / x = 1 / 2014)
    (h3 : 2 * z - 2 * x + 1 / y = 1 / 2014) :
    x = 2014 ∧ y = 2014 ∧ z = 2014 := by
  -- Simplify expressions assuming x, y, z are positive
  refine' ⟨_, _, _⟩ <;> field_simp at h1 h2 h3  <;>
    -- Use arithmetic manipulation to derive initial relationship
    nlinarith [mul_pos hx hy, mul_pos hy hz, mul_pos hz hx]