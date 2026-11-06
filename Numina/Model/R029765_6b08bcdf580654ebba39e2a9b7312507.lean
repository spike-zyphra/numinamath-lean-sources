import Mathlib

theorem inequalities_31162 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x ^ 3 / (x + y) + y ^ 3 / (y + z) + z ^ 3 / (z + x) ≥
    (x * y + y * z + z * x) / 2 := by
  have h1 : 0 < x + y := by nlinarith
  have h2 : 0 < y + z := by nlinarith
  have h3 : 0 < z + x := by nlinarith

  have h4 : x ^ 3 / (x + y) + y ^ 3 / (y + z) + z ^ 3 / (z + x) - (x * y + y * z + z * x) / 2 ≥ 0 := by
    have h5 : x + y > 0 := by nlinarith
    have h6 : y + z > 0 := by nlinarith
    have h7 : z + x > 0 := by nlinarith

    have h8 : x ^ 3 / (x + y) + y ^ 3 / (y + z) + z ^ 3 / (z + x) - (x * y + y * z + z * x) / 2 = 
      (x ^ 3 * (y + z) * (z + x) + y ^ 3 * (x + y) * (z + x) + z ^ 3 * (x + y) * (y + z) - (x * y + y * z + z * x) / 2 * (x + y) * (y + z) * (z + x)) / ((x + y) * (y + z) * (z + x)) := by
      field_simp
      ring_nf
      <;> field_simp <;> ring_nf
      <;> field_simp <;> ring_nf
      <;> field_simp <;> ring_nf

    rw [h8]

    apply div_nonneg

    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (y * (y - x)), sq_nonneg (y * (y - z)), sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)), 
      mul_pos hx hy, mul_pos hy hz, mul_pos hz hx
    ]

    have h2' : (x + y) * (y + z) * (z + x) > 0 := by
      apply mul_pos
      apply mul_pos
      all_goals nlinarith
    positivity

  linarith