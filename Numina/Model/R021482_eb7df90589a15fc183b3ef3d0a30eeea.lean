import Mathlib

theorem inequalities_600296 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z = 1) :
    (1 / x - x) * (1 / y - y) * (1 / z - z) ≥ (8 / 3) ^ 3 := by

  have hx1 : x * y * z > 0 := by positivity
  have h1 : (1 / x - x) * (1 / y - y) * (1 / z - z) = ((1 - x^2) * (1 - y^2) * (1 - z^2)) / (x * y * z) := by
    field_simp
    <;> ring
  rw [h1]

  have h2 : (1 - x^2) * (1 - y^2) * (1 - z^2) ≥ (8 / 3) ^ 3 * (x * y * z) := by 
    have h3 : z = 1 - x - y := by linarith 
    rw [h3]
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - (1 - x - y)), sq_nonneg (y - (1 - x - y)), 
      sq_nonneg (x * y - y * (1 - x - y)), sq_nonneg (x * y - x * (1 - x - y)), sq_nonneg (x * (1 - x - y) - y * (1 - x - y)), 
      mul_pos hx hy, mul_pos hx (show 0 < 1 - x - y by nlinarith), 
      mul_pos hy (show 0 < 1 - x - y by nlinarith), 
      mul_pos (show 0 < x * y by nlinarith) (show 0 < x * (1 - x - y) by nlinarith), 
      mul_pos (show 0 < x * y by nlinarith) (show 0 < y * (1 - x - y) by nlinarith), 
      mul_pos (show 0 < x * (1 - x - y) by nlinarith) (show 0 < y * (1 - x - y) by nlinarith)]

  have h3 : ((1 - x^2) * (1 - y^2) * (1 - z^2)) / (x * y * z) ≥ (8 / 3) ^ 3 := by 
    apply (le_div_iff₀ (by positivity)).mpr 
    nlinarith [h2]

  linarith [h3]