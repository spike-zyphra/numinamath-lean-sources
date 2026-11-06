import Mathlib

theorem algebra_121474 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : 2 * x - 2 * y + 1 / z = 1 / 2014) (h2 : 2 * y - 2 * z + 1 / x = 1 / 2014)
    (h3 : 2 * z - 2 * x + 1 / y = 1 / 2014) :
    x = 2014 ∧ y = 2014 ∧ z = 2014 := by
  have h4 : 1 / x + 1 / y + 1 / z = 3 / 2014 := by
    have h : (2 * x - 2 * y + 1 / z) + (2 * y - 2 * z + 1 / x) + (2 * z - 2 * x + 1 / y) = 3 / 2014 := by
      linarith
    have h' : (2 * x - 2 * y + 1 / z) + (2 * y - 2 * z + 1 / x) + (2 * z - 2 * x + 1 / y) = 1 / x + 1 / y + 1 / z := by
      ring
    rw [h'] at h
    linarith
  have h5 : x = 2014 := by
    field_simp at h1 h2 h3 h4
    nlinarith [sq_nonneg (x - 2014), sq_nonneg (y - 2014), sq_nonneg (z - 2014),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
    ]
  have h6 : y = 2014 := by
    field_simp at h1 h2 h3 h4
    nlinarith [sq_nonneg (x - 2014), sq_nonneg (y - 2014), sq_nonneg (z - 2014),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
    ]
  have h7 : z = 2014 := by
    field_simp at h1 h2 h3 h4
    nlinarith [sq_nonneg (x - 2014), sq_nonneg (y - 2014), sq_nonneg (z - 2014),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
    ]
  exact ⟨h5, h6, h7⟩