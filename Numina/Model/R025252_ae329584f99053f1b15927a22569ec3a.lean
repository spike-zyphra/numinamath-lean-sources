import Mathlib

theorem inequalities_260896 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 1) :
    x^2 / (y + z) + y^2 / (z + x) + z^2 / (x + y) ≥
    ((x^2 + y^2) / (x + y) + (y^2 + z^2) / (y + z) + (z^2 + x^2) / (z + x)) / 2 ∧
    ((x^2 + y^2) / (x + y) + (y^2 + z^2) / (y + z) + (z^2 + x^2) / (z + x)) / 2 ≥
    (x + y + z) / 2 ∧ (x + y + z) / 2 ≥ 3 / 2 := by

  constructor
  · -- First, show that $\frac{x^2}{y+z} + \frac{y^2}{z+x} + \frac{z^2}{x+y} \geq \frac{1}{2}\left(\frac{x^2+y^2}{x+y} + \frac{y^2+z^2}{y+z} + \frac{z^2+x^2}{z+x}\right)$.
    have h1 : x^2 / (y + z) + y^2 / (z + x) + z^2 / (x + y) - (( (x^2 + y^2) / (x + y) + (y^2 + z^2) / (y + z) + (z^2 + x^2) / (z + x) ) / 2) ≥ 0 := by
      have hx1 : 0 < y + z := by linarith
      have hx2 : 0 < z + x := by linarith
      have hx3 : 0 < x + y := by linarith
      have h1 : 0 < (y + z) * (z + x) * (x + y) := by positivity
      have h3 : x^2 / (y + z) + y^2 / (z + x) + z^2 / (x + y) - (( (x^2 + y^2) / (x + y) + (y^2 + z^2) / (y + z) + (z^2 + x^2) / (z + x) ) / 2) =
          ( (x^2 * (z + x) * (x + y) + y^2 * (y + z) * (x + y) + z^2 * (y + z) * (z + x) ) * 2 - ( (x^2 + y^2) * (y + z) * (z + x) + (y^2 + z^2) * (z + x) * (x + y) + (z^2 + x^2) * (y + z) * (x + y) ) ) / ( 2 * (y + z) * (z + x) * (x + y) ) := by
        field_simp
        ring
      rw [h3]
      apply div_nonneg
      have h4 : ( (x^2 * (z + x) * (x + y) + y^2 * (y + z) * (x + y) + z^2 * (y + z) * (z + x) ) * 2 - ( (x^2 + y^2) * (y + z) * (z + x) + (y^2 + z^2) * (z + x) * (x + y) + (z^2 + x^2) * (y + z) * (x + y) ) ) ≥ 0 := by
        nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
                  sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
                  sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)),
                  sq_nonneg (y * (y - z)), sq_nonneg (y * (y - x)),
                  sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)),
                  mul_pos hx hy, mul_pos hx hz, mul_pos hy hz ]
      linarith
      all_goals positivity
    linarith only [h1]

  constructor
  · -- Show that $\frac{1}{2}\left(\frac{x^2+y^2}{x+y} + \frac{y^2+z^2}{y+z} + \frac{z^2+x^2}{z+x}\right) \geq \frac{x+y+z}{2}$.
    have h2 : ((x^2 + y^2) / (x + y) + (y^2 + z^2) / (y + z) + (z^2 + x^2) / (z + x)) / 2 ≥ (x + y + z) / 2 := by
      have h2'1 : (x^2 + y^2) / (x + y) ≥ (x + y) / 2 := by
        have hx4 : x + y > 0 := by positivity
        apply (le_div_iff₀ hx4).mpr
        nlinarith [sq_nonneg (x - y), sq_nonneg (x - y), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x * y - y * x)]
      have h2'2 : (y^2 + z^2) / (y + z) ≥ (y + z) / 2 := by
        have hyz4 : y + z > 0 := by positivity
        apply (le_div_iff₀ hyz4).mpr
        nlinarith [sq_nonneg (y - z), sq_nonneg (y - z), sq_nonneg (y ^ 2 - z ^ 2), sq_nonneg (y * z - z * y)]
      have h2'3 : (z^2 + x^2) / (z + x) ≥ (z + x) / 2 := by
        have hzx4 : z + x > 0 := by positivity
        apply (le_div_iff₀ hzx4).mpr
        nlinarith [sq_nonneg (z - x), sq_nonneg (z - x), sq_nonneg (z ^ 2 - x ^ 2), sq_nonneg (z * x - x * z)]
      linarith
    linarith only [h2]
  · -- Show that $\frac{x+y+z}{2} \geq \frac{3}{2}$.
    have h3 : (x + y + z) / 2 ≥ 3 / 2 := by
      have h4 : x + y + z ≥ 3 := by
        nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, hxyz]
      linarith
    linarith