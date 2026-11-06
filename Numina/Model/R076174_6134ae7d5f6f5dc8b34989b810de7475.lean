import Mathlib

theorem inequalities_318096 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    0 ≤ (z^2 - x^2) / (x + y) + (x^2 - y^2) / (y + z) + (y^2 - z^2) / (z + x) := by
  have h1 : 0 < x + y := by
    linarith [hx, hy]
  have h2 : 0 < y + z := by
    linarith [hy, hz]
  have h3 : 0 < z + x := by
    linarith [hz, hx]
  have h4 : (z^2 - x^2) / (x + y) + (x^2 - y^2) / (y + z) + (y^2 - z^2) / (z + x) =
          ( (z^2 - x^2) * (y + z) * (z + x) + (x^2 - y^2) * (x + y) * (z + x) + (y^2 - z^2) * (x + y) * (y + z) ) / ( (x + y) * (y + z) * (z + x) ) := by
      field_simp [h1, h2, h3]
      <;> ring
  rw [h4]

  have h5 : 0 < (x + y) * (y + z) * (z + x) := by
      positivity
  have h6 : (z^2 - x^2) * (y + z) * (z + x) + (x^2 - y^2) * (x + y) * (z + x) + (y^2 - z^2) * (x + y) * (y + z) ≥ 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x + y - z), sq_nonneg (y + z - x), sq_nonneg (z + x - y),
          mul_pos hx hy, mul_pos hy hz, mul_pos hz hx]
  apply div_nonneg h6 (show 0 ≤ (x + y) * (y + z) * (z + x) by positivity)