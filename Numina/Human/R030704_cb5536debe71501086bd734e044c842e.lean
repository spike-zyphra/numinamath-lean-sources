import Mathlib

/- Problem 3. Let $x, y, z$ be strictly positive real numbers. Show that:

a) $\frac{x^{2}}{y\left(x^{2}+x y+y^{2}\right)} \geq \frac{2 x-y}{3 x y}$
b) $\frac{x^{2}}{y\left(x^{2}+x y+y^{2}\right)}+\frac{y^{2}}{z\left(y^{2}+y z+z^{2}\right)}+\frac{z^{2}}{x\left(z^{2}+x z+x^{2}\right)} \geq \frac{x y+y z+x z}{3 x y z}$. -/
theorem inequalities_109808 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (x^2 / (y * (x^2 + x * y + y^2)) ≥ (2 * x - y) / (3 * x * y)) ∧
    (x^2 / (y * (x^2 + x * y + y^2)) + y^2 / (z * (y^2 + y * z + z^2)) +
     z^2 / (x * (z^2 + x * z + x^2)) ≥ (x * y + y * z + x * z) / (3 * x * y * z)) := by
  -- Split the proof into two parts (a and b)
  constructor
  -- Part a: Prove the first inequality
  ·
    -- Prove that x^2/(y(x^2+xy+y^2)) ≥ (2x-y)/(3xy)
    have h1 : x^2 / (y * (x^2 + x * y + y^2)) ≥ (2 * x - y) / (3 * x * y) := by
      -- Apply division inequality transformation
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      -- Use nonlinear arithmetic with the fact that (x-y)² ≥ 0 and xy > 0
      nlinarith [sq_nonneg (x - y), mul_pos hx hy]
    exact h1
  -- Part b: Prove the second inequality
  ·
    -- Reuse the first inequality for x and y
    have h1 : x^2 / (y * (x^2 + x * y + y^2)) ≥ (2 * x - y) / (3 * x * y) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [sq_nonneg (x - y), mul_pos hx hy]
    -- Prove similar inequality with y and z
    have h2 : y^2 / (z * (y^2 + y * z + z^2)) ≥ (2 * y - z) / (3 * y * z) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [sq_nonneg (y - z), mul_pos hy hz]
    -- Prove similar inequality with z and x
    have h3 : z^2 / (x * (z^2 + x * z + x^2)) ≥ (2 * z - x) / (3 * z * x) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [sq_nonneg (z - x), mul_pos hz hx]
    -- Show that the sum of the right sides equals (xy+yz+xz)/(3xyz)
    have h4 : (2 * x - y) / (3 * x * y) + (2 * y - z) / (3 * y * z) + (2 * z - x) / (3 * z * x) = (x * y + y * z + x * z) / (3 * x * y * z) := by
      field_simp
      ring
    -- Combine all inequalities to complete the proof
    linarith
