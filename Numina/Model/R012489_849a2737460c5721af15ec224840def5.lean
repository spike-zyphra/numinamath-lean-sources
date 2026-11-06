import Mathlib

theorem inequalities_292805 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z ≥ 1 / x + 1 / y + 1 / z) :
    x / y + y / z + z / x ≥ 1 / x / y + 1 / y / z + 1 / z / x := by

  have h1 : x * y * z > 0 := by
    positivity

  have h4 : x * y * z * (1 / x + 1 / y + 1 / z) = x * y + x * z + y * z := by
    field_simp
    <;> ring

  have h5 : x * y * z * (x + y + z) ≥ x * y + x * z + y * z := by
    have h6 : x * y * z * (x + y + z) ≥ x * y * z * (1 / x + 1 / y + 1 / z) := by
      have h4 : x * y * z > 0 := h1
      have h8 : x + y + z ≥ 1 / x + 1 / y + 1 / z := h
      nlinarith [h8, h1]

    nlinarith [h6, h4]

  have h6 : x / y + y / z + z / x - (1 / x / y + 1 / y / z + 1 / z / x) ≥ 0 := by

    have h7 : x / y + y / z + z / x - (1 / x / y + 1 / y / z + 1 / z / x) =
        (x^2 * z + y^2 * x + z^2 * y - (x + y + z)) / (x * y * z) := by
      field_simp
      ring

    have h8 : x^2 * z + y^2 * x + z^2 * y ≥ x + y + z := by
      nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
        sq_nonneg (x * y), sq_nonneg (y * z), sq_nonneg (z * x), 
        mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, h5]

    have h9 : x * y * z > 0 := h1

    rw [h7] at *
    apply div_nonneg
    linarith
    all_goals
      positivity

  linarith