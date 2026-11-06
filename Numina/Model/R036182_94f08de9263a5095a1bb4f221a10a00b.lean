import Mathlib

theorem inequalities_600794 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : x^2 + y^2 + z^2 = 1) :
    x^2 / (1 - y * z) + y^2 / (1 - z * x) + z^2 / (1 - x * y) ≤ 3 / 2 := by
  have h1 : 0 < 1 - y * z := by
    nlinarith [sq_nonneg (y - z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (x + y + z), h]
  have h2 : 0 < 1 - z * x := by
    nlinarith [sq_nonneg (z - x), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (x + y + z), h]
  have h3 : 0 < 1 - x * y := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y + z), h]
  have h4 : x^2 / (1 - y * z) + y^2 / (1 - z * x) + z^2 / (1 - x * y) - 3 / 2 ≤ 0 := by
    have h5 : x^2 / (1 - y * z) + y^2 / (1 - z * x) + z^2 / (1 - x * y) - 3 / 2 =
        (x^2 * (1 - z * x) * (1 - x * y) + y^2 * (1 - y * z) * (1 - x * y) + z^2 * (1 - y * z) * (1 - z * x) - 3 / 2 * (1 - y * z) * (1 - z * x) * (1 - x * y)) / ((1 - y * z) * (1 - z * x) * (1 - x * y)) := by
      field_simp
      ring
    rw [h5]
    apply div_nonpos_of_nonpos_of_nonneg
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
      mul_nonneg hx hy, mul_nonneg hy hz, mul_nonneg hz hx, 
      mul_nonneg (show 0 ≤ x * y by nlinarith) (show 0 ≤ y * z by nlinarith), 
      mul_nonneg (show 0 ≤ y * z by nlinarith) (show 0 ≤ z * x by nlinarith), 
      mul_nonneg (show 0 ≤ z * x by nlinarith) (show 0 ≤ x * y by nlinarith)
    ]
    positivity
  linarith