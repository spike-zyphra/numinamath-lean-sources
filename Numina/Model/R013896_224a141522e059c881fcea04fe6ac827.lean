import Mathlib

open Real

theorem inequalities_83532 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z = 1) :
    (1 + 1 / x) * (1 + 1 / y) * (1 + 1 / z) ≥ 64 := by
  have h1 : (1 + 1 / x) * (1 + 1 / y) * (1 + 1 / z) = (x + 1) * (y + 1) * (z + 1) / (x * y * z) := by
    field_simp
    <;> ring
  rw [h1]
  have h2 : 0 < x * y * z := by positivity
  have h3' : (x + 1) * (y + 1) * (z + 1) = (x * y * z) + (x * y + x * z + y * z) + (x + y + z) + 1 := by
    ring
  have h5 : (x + y + z) = 1 := by linarith 
  have h8 : (x + 1) * (y + 1) * (z + 1) = (x * y * z) + (x * y + x * z + y * z) + 1 + 1 := by 
    rw [h3']
    nlinarith [h5]
  have h10 : (x * y * z) + (x * y + x * z + y * z) + 1 + 1 ≥ 64 * (x * y * z) := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
          sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
          mul_pos (show 0 < y * z by nlinarith) (show 0 < x by linarith), 
          sq_nonneg (x * y), sq_nonneg (y * z), sq_nonneg (z * x)
        ]
  have h11 : (x + 1) * (y + 1) * (z + 1) ≥ 64 * (x * y * z) := by
    linarith [h8, h10]
  have h12 : (x + 1) * (y + 1) * (z + 1) / (x * y * z) ≥ 64 := by
    have h10 : (x + 1) * (y + 1) * (z + 1) ≥ 64 * (x * y * z) := h11
    have h11 : 0 < x * y * z := h2
    apply (le_div_iff₀ h11).mpr 
    nlinarith
  linarith