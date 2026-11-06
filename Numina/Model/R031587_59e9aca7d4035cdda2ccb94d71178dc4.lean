import Mathlib

theorem algebra_266416 {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x^2 + y^2 + Real.sqrt 3 * x * y = 20 + 8 * Real.sqrt 3) (h2 : y^2 + z^2 = 13)
    (h3 : z^2 + x^2 + x * z = 37) :
    x = 4 ∧ y = 2 ∧ z = 3 := by
  have h4 : (x - 4) ^ 2 + (y - 2) ^ 2 + (z - 3) ^ 2 = 0 := by
    nlinarith [sq_nonneg (y - 2), sq_nonneg (z - 3), sq_nonneg (x - 4), 
              mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
              sq_nonneg (x * y - 4 * 2), sq_nonneg (x * z - 4 * 3), sq_nonneg (y * z - 2 * 3), 
              Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
  have hx4 : x - 4 = 0 := by
    nlinarith [sq_nonneg (x - 4), sq_nonneg (y - 2), sq_nonneg (z - 3), h4]
  have hx4' : x = 4 := by linarith
  have hy2 : y - 2 = 0 := by
    nlinarith [sq_nonneg (y - 2), sq_nonneg (z - 3), sq_nonneg (x - 4), h4]
  have hy2' : y = 2 := by linarith
  have hz3 : z - 3 = 0 := by
    nlinarith [sq_nonneg (z - 3), sq_nonneg (x - 4), sq_nonneg (y - 2), h4]
  have hz3' : z = 3 := by linarith
  exact ⟨hx4', hy2', hz3'⟩