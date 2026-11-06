import Mathlib
theorem inequalities_323830 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    0 ≤ (y ^ 2 - x ^ 2) / (z + x) + (z ^ 2 - y ^ 2) / (x + y) + (x ^ 2 - z ^ 2) / (y + z) := by

  have h1 : 0 < z + x := by linarith
  have h2 : 0 < x + y := by linarith
  have h3 : 0 < y + z := by linarith

  have h4 : 0 < (z + x) * (x + y) * (y + z) := by
    positivity

  have h5 : (y ^ 2 - x ^ 2) / (z + x) + (z ^ 2 - y ^ 2) / (x + y) + (x ^ 2 - z ^ 2) / (y + z) ≥ 0 := by
    have pos1 : 0 < (z + x) * (x + y) * (y + z) := h4
    have h6 : (y ^ 2 - x ^ 2) / (z + x) + (z ^ 2 - y ^ 2) / (x + y) + (x ^ 2 - z ^ 2) / (y + z) =
        ( (y ^ 2 - x ^ 2) * (x + y) * (y + z) + (z ^ 2 - y ^ 2) * (z + x) * (y + z) + (x ^ 2 - z ^ 2) * (z + x) * (x + y) ) / ((z + x) * (x + y) * (y + z)) := by
      field_simp
      <;> ring
    rw [h6] at *
    apply div_nonneg
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x + y - z), sq_nonneg (x + z - y), sq_nonneg (y + z - x),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
      mul_pos h1 h2, mul_pos h1 h3, mul_pos h2 h3 ]
    positivity
  linarith [h5]