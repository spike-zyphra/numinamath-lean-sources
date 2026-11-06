import Mathlib

theorem inequalities_273788 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : y ≤ x) (hyz : z ≤ y) :
    3 ≤ (x + y + z) * (x + y - z) * (x - y + z) / (x * y * z) := by
  have h1 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    exact hx
    exact hy
    exact hz

  have h2 : (x + y + z) * (x + y - z) * (x - y + z) ≥ 3 * (x * y * z) := by
    have hx2 : 0 ≤ x - y := by linarith
    have hy2 : 0 ≤ y - z := by linarith
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z),
          sq_nonneg (x + y - z), sq_nonneg (x - y + z), sq_nonneg (x + y + z),
          mul_pos hx hy, mul_pos hy hz, mul_pos hx hz, 
          mul_nonneg (show 0 ≤ x - y by linarith) (show 0 ≤ y - z by linarith), 
          mul_nonneg (show 0 ≤ x - y by linarith) (show 0 ≤ z by linarith), 
          mul_nonneg (show 0 ≤ y - z by linarith) (show 0 ≤ z by linarith), 
          sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
          mul_nonneg (show 0 ≤ x - y by linarith) (show 0 ≤ y - z by linarith)
        ]

  have h3 : (x + y + z) * (x + y - z) * (x - y + z) / (x * y * z) ≥ 3 := by
    apply (le_div_iff₀ (by positivity)).mpr
    linarith
  linarith [h3]