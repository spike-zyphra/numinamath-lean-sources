import Mathlib

theorem algebra_75705 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : 2 * x - 2 * y + 1 / z = 1 / 2014) (h2 : 2 * y - 2 * z + 1 / x = 1 / 2014)
    (h3 : 2 * z - 2 * x + 1 / y = 1 / 2014) :
    x = 2014 ∧ y = 2014 ∧ z = 2014 := by

  have eq1' : (2 * x - 2 * y) * (2014 * z) + 2014 = z := by
    have h11 : z ≠ 0 := by linarith
    field_simp at h1 ⊢
    nlinarith
  have eq2' : (2 * y - 2 * z) * (2014 * x) + 2014 = x := by
    have h22 : x ≠ 0 := by linarith
    field_simp at h2 ⊢
    nlinarith
  have eq3' : (2 * z - 2 * x) * (2014 * y) + 2014 = y := by
    have h33 : y ≠ 0 := by linarith
    field_simp at h3 ⊢
    nlinarith
  have h4 : x = 2014 := by
    nlinarith [sq_nonneg (x - 2014), sq_nonneg (y - 2014), sq_nonneg (z - 2014),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
    ]
  have h5 : y = 2014 := by
    nlinarith [sq_nonneg (x - 2014), sq_nonneg (y - 2014), sq_nonneg (z - 2014),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
    ]
  have h6 : z = 2014 := by
    nlinarith [sq_nonneg (x - 2014), sq_nonneg (y - 2014), sq_nonneg (z - 2014),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
    ]
  exact ⟨h4, h5, h6⟩