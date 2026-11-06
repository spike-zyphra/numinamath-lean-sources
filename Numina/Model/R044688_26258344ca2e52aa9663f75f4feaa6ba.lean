import Mathlib

theorem inequalities_292784 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 8) :
    (x - 2) / (x + 1) + (y - 2) / (y + 1) + (z - 2) / (z + 1) ≤ 0 := by
  have h1 : (x - 2) / (x + 1) + (y - 2) / (y + 1) + (z - 2) / (z + 1) =
      3 - 3 * (1 / (x + 1) + 1 / (y + 1) + 1 / (z + 1)) := by
    field_simp [(show x + 1 ≠ 0 by linarith), (show y + 1 ≠ 0 by linarith), (show z + 1 ≠ 0 by linarith)]
    ring
  rw [h1] at *
  -- Prove that $\frac{1}{x+1} + \frac{1}{y+1} + \frac{1}{z+1} \geq 1$
  have h2 : 1 / (x + 1) + 1 / (y + 1) + 1 / (z + 1) - 1 ≥ 0 := by
    have hx1 : 0 < x + 1 := by linarith
    have hy1 : 0 < y + 1 := by linarith
    have hz1 : 0 < z + 1 := by linarith
    have hx2 : x + 1 > 0 := by linarith
    have hy2 : y + 1 > 0 := by linarith
    have hz2 : z + 1 > 0 := by linarith
    have h3 : (y + 1) * (z + 1) + (x + 1) * (z + 1) + (x + 1) * (y + 1) ≥ (x + 1) * (y + 1) * (z + 1) := by
      nlinarith [sq_nonneg (x * y - 4), sq_nonneg (y * z - 4), sq_nonneg (z * x - 4),
                sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (z - 2),
                mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, hxyz]
    have h4 : (y + 1) * (z + 1) + (x + 1) * (z + 1) + (x + 1) * (y + 1) - (x + 1) * (y + 1) * (z + 1) ≥ 0 := by
      linarith
    have h5 : 1 / (x + 1) + 1 / (y + 1) + 1 / (z + 1) - 1 =
        ((y + 1) * (z + 1) + (x + 1) * (z + 1) + (x + 1) * (y + 1) - (x + 1) * (y + 1) * (z + 1)) / ((x + 1) * (y + 1) * (z + 1)) := by
      field_simp
      ring
    rw [h5]
    apply div_nonneg
    linarith
    all_goals positivity
  linarith