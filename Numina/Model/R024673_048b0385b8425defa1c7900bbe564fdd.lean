import Mathlib

theorem inequalities_251661 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z = 1) :
    (1 + 1 / x) * (1 + 1 / y) * (1 + 1 / z) ≥ 64 := by
  have h1 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    exact hx
    exact hy
    exact hz
  have h2 : (1 + 1 / x) * (1 + 1 / y) * (1 + 1 / z) = (x + 1) * (y + 1) * (z + 1) / (x * y * z) := by 
    field_simp
    <;> ring
  rw [h2]
  have h3 : (x + 1) * (y + 1) * (z + 1) ≥ 64 * (x * y * z) := by
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      h, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  have h5 : (x + 1) * (y + 1) * (z + 1) / (x * y * z) ≥ 64 := by
    apply (le_div_iff₀ (by positivity)).mpr 
    nlinarith [h3, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  linarith [h5]