import Mathlib

theorem inequalities_256225 (x y z : ℝ) (h : x * y * z = 1) :
    x^2 + y^2 + z^2 ≥ 1 / x + 1 / y + 1 / z := by
  have hx : x ≠ 0 := by
    by_contra hx'
    rw [hx'] at h
    nlinarith
  have hy : y ≠ 0 := by
    by_contra hy'
    rw [hy'] at h
    nlinarith
  have hz : z ≠ 0 := by
    by_contra hz'
    rw [hz'] at h
    nlinarith
  have h1 : x * y * z = 1 := h
  have h3 : x * y * z > 0 := by
    have h2 : x * y * z = 1 := h
    nlinarith [sq_nonneg (x * y * z), sq_nonneg (x * y * z)]
  have eq1 : x^2 + y^2 + z^2 - (1 / x + 1 / y + 1 / z) =
      ( (x^2 + y^2 + z^2) * (x * y * z) - (y * z + x * z + x * y) ) / (x * y * z) := by
    field_simp [hx, hy, hz]
    <;> ring
  have h4 : ( (x^2 + y^2 + z^2) * (x * y * z) - (y * z + x * z + x * y) ) ≥ 0 := by
    have h2 : x * y * z = 1 := h
    have h5 : x * y * z = 1 := h
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x * y * z - 1),
      sq_nonneg (x * y + x * z + y * z - 3),
      sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1)
    ]
  have h5 : ( (x^2 + y^2 + z^2) * (x * y * z) - (y * z + x * z + x * y) ) / (x * y * z) ≥ 0 := by
    apply div_nonneg
    linarith
    positivity
  have h6 : x^2 + y^2 + z^2 - (1 / x + 1 / y + 1 / z) ≥ 0 := by
    linarith [eq1, h5]
  linarith