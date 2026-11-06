import Mathlib

theorem inequalities_601678 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 1) :
    2 ≤ (x^3 + y^3) / (x^2 + x * y + y^2) + (y^3 + z^3) / (y^2 + y * z + z^2) +
        (z^3 + x^3) / (z^2 + z * x + x^2) := by
  have h4 : (x^3 + y^3) / (x^2 + x * y + y^2) ≥ (x + y) / 3 := by
    have hx5 : 0 < (x^2 + x * y + y^2 : ℝ) := by
      nlinarith [show 0 < x from hx, show 0 < y from hy]

    apply (le_div_iff₀ hx5).mpr
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy]

  have h5 : (y^3 + z^3) / (y^2 + y * z + z^2) ≥ (y + z) / 3 := by
    have hy5 : 0 < (y^2 + y * z + z^2 : ℝ) := by 
      nlinarith [show 0 < y from hy, show 0 < z from hz]

    apply (le_div_iff₀ hy5).mpr
    nlinarith [sq_nonneg (y - z), sq_nonneg (y + z), mul_pos hy hz]

  have h6 : (z^3 + x^3) / (z^2 + z * x + x^2) ≥ (z + x) / 3 := by
    have hz5 : 0 < (z^2 + z * x + x^2 : ℝ) := by 
      nlinarith [show 0 < z from hz, show 0 < x from hx]

    apply (le_div_iff₀ hz5).mpr
    nlinarith [sq_nonneg (z - x), sq_nonneg (z + x), mul_pos hz hx]

  have h7 : (x^3 + y^3) / (x^2 + x * y + y^2) + (y^3 + z^3) / (y^2 + y * z + z^2) + (z^3 + x^3) / (z^2 + z * x + x^2) ≥ 2 * (x + y + z) / 3 := by
    linarith [h4, h5, h6]
  
  have hx8 : x + y + z ≥ 3 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
      mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, hxyz]

  linarith [h7, hx8]