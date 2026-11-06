import Mathlib

theorem inequalities_90279 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : 1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z) = 2) : 8 * x * y * z ≤ 1 := by
  have h1 : 0 < (1 + x) * (1 + y) * (1 + z) := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have h2 : 1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z) = 2 := h
  have eq1 : (1 + y) * (1 + z) + (1 + x) * (1 + z) + (1 + x) * (1 + y) = 2 * (1 + x) * (1 + y) * (1 + z) := by
    have hx' : (1 + x) ≠ 0 := by linarith
    have hy' : (1 + y) ≠ 0 := by linarith
    have hz' : (1 + z) ≠ 0 := by linarith
    field_simp [hx', hy', hz'] at h2 ⊢
    nlinarith [h2, h1, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  have eq2 : x * y + x * z + y * z + 2 * x * y * z = 1 := by
    nlinarith [eq1]
  nlinarith [sq_nonneg (x * y - x * z), sq_nonneg (x * y - y * z), sq_nonneg (x * z - y * z),
      sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, sq_nonneg (x * y * z - 1 / 8)]