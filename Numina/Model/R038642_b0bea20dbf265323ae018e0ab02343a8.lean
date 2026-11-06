import Mathlib

theorem inequalities_597177 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x * y / (z * (z + x)) + y * z / (x * (x + y)) + z * x / (y * (y + z)) ≥
    x / (z + x) + y / (x + y) + z / (y + z) := by
  have h1 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    all_goals nlinarith

  have h2 : 0 < z * (z + x) := by
    positivity

  have h3 : 0 < x * (x + y) := by
    positivity

  have h4 : 0 < y * (y + z) := by
    positivity

  have h5 : x * y / (z * (z + x)) - x / (z + x) =
      x * (y - z) / (z * (z + x)) := by
    field_simp
    <;> ring

  have h6 : y * z / (x * (x + y)) - y / (x + y) =
      y * (z - x) / (x * (x + y)) := by
    field_simp
    <;> ring

  have h7 : z * x / (y * (y + z)) - z / (y + z) =
      z * (x - y) / (y * (y + z)) := by
    field_simp
    <;> ring

  suffices x * (y - z) / (z * (z + x)) + y * (z - x) / (x * (x + y)) + z * (x - y) / (y * (y + z)) ≥ 0 by
    linarith [this, h5, h6, h7]

  have h8 : 0 < x * y * z * (x + y) * (y + z) * (z + x) := by
    positivity

  have h9 : x * (y - z) / (z * (z + x)) + y * (z - x) / (x * (x + y)) + z * (x - y) / (y * (y + z)) ≥ 0 := by
    have h10 : x * (y - z) / (z * (z + x)) + y * (z - x) / (x * (x + y)) + z * (x - y) / (y * (y + z)) =
        (x ^ 2 * y * (y - z) * (x + y) * (y + z) + y ^ 2 * z * (z - x) * (y + z) * (z + x) + x * z ^ 2 * (x - y) * (x + y) * (z + x)) / (x * y * z * (x + y) * (y + z) * (z + x)) := by
      field_simp
      ring
    rw [h10]

    apply div_nonneg
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)),
      sq_nonneg (y * (y - x)), sq_nonneg (y * (y - z)),
      sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)),
      mul_pos hx hy, mul_pos hy hz, mul_pos hz hx,
      mul_pos hx (show 0 < x + y by nlinarith),
      mul_pos hx (show 0 < x + z by nlinarith),
      mul_pos hy (show 0 < y + z by nlinarith)]
    positivity

  exact h9