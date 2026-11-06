import Mathlib

theorem inequalities_116656 (x y z : ℝ) (hx : 0 < z) (hy : z ≤ y) (hxy : y ≤ x) :
    x^2 * y / z + y^2 * z / x + z^2 * x / y ≥ x^2 + y^2 + z^2 := by
  have h1 : 0 < x := by linarith
  have h2 : 0 < y := by linarith
  have h3 : 0 < x * y * z := by
    positivity

  have h4 : x^2 * y / z + y^2 * z / x + z^2 * x / y - (x^2 + y^2 + z^2) ≥ 0 := by
    have h5 : x^2 * y / z + y^2 * z / x + z^2 * x / y - (x^2 + y^2 + z^2) =
        (x^3 * y^2 + y^3 * z^2 + z^3 * x^2 - (x^3 * y * z + x * y^3 * z + x * y * z^3)) / (x * y * z) := by
      field_simp
      ring
    rw [h5]
    have h6 : x^3 * y^2 + y^3 * z^2 + z^3 * x^2 ≥ x^3 * y * z + x * y^3 * z + x * y * z^3 := by
      nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x * (x - y)), sq_nonneg (x * (y - z)), sq_nonneg (y * (x - y)), sq_nonneg (y * (y - z)),
          sq_nonneg (z * (x - y)), sq_nonneg (z * (y - z)), mul_nonneg (show 0 ≤ x - y by nlinarith) (show 0 ≤ y - z by nlinarith),
          mul_nonneg (show 0 ≤ x - y by nlinarith) (show 0 ≤ z by linarith), mul_nonneg (show 0 ≤ y - z by nlinarith) (show 0 ≤ z by linarith),
          mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ y - z by nlinarith), 
          mul_nonneg (show 0 ≤ y by linarith) (show 0 ≤ x - y by nlinarith)]
    have h7 : (x^3 * y^2 + y^3 * z^2 + z^3 * x^2 - (x^3 * y * z + x * y^3 * z + x * y * z^3 : ℝ)) ≥ 0 := by
      linarith
    have h8 : x * y * z > 0 := by positivity
    have h9 : (x^3 * y^2 + y^3 * z^2 + z^3 * x^2 - (x^3 * y * z + x * y^3 * z + x * y * z^3 : ℝ)) / (x * y * z) ≥ 0 := by
      apply div_nonneg
      linarith
      all_goals positivity
    linarith
  linarith