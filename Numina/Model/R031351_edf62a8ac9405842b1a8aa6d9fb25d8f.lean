import Mathlib
theorem algebra_607474 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z ≥ 1 / x + 1 / y + 1 / z) :
    x / y + y / z + z / x ≥ 1 / (x * y) + 1 / (y * z) + 1 / (z * x):= by
  have h1 : 0 < x * y * z := by positivity

  have h2 : (x + y + z) * (x * y * z) ≥ x * y + x * z + y * z := by
    have h3 : x + y + z ≥ 1 / x + 1 / y + 1 / z := h
    have h4 : 1 / x + 1 / y + 1 / z = (y * z + x * z + x * y) / (x * y * z) := by
      field_simp
      <;> ring
    rw [h4] at h3
    have h5 : (x + y + z) * (x * y * z) ≥ y * z + x * z + x * y := by
      have h6 : x * y * z > 0 := by positivity
      apply (div_le_iff₀ (by positivity)).mp at h3
      linarith
    linarith

  have h3 : x / y + y / z + z / x - (1 / (x * y) + 1 / (y * z) + 1 / (z * x)) ≥ 0 := by
    have pos1 : 0 < x * y * z := h1
    have h4 : x / y + y / z + z / x - (1 / (x * y) + 1 / (y * z) + 1 / (z * x)) = 
        (x^2 * z + y^2 * x + z^2 * y - (x + y + z)) / (x * y * z) := by
      field_simp
      ring
    rw [h4] at *
    have h4 : x^2 * z + y^2 * x + z^2 * y ≥ x + y + z := by
      nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
          sq_nonneg (x * y), sq_nonneg (y * z), sq_nonneg (z * x),
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
          h2, 
          mul_pos (show 0 < x * y from mul_pos hx hy) (show 0 < x * z from mul_pos hx hz), 
          mul_pos (show 0 < x * y from mul_pos hx hy) (show 0 < y * z from mul_pos hy hz), 
          mul_pos (show 0 < y * z from mul_pos hy hz) (show 0 < x * z from mul_pos hx hz)
        ]
    have h5 : x^2 * z + y^2 * x + z^2 * y - (x + y + z) ≥ 0 := by linarith [h4]
    apply div_nonneg
    linarith
    all_goals linarith
  linarith