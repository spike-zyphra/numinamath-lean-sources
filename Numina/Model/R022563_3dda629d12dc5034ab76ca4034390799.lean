import Mathlib
open Real

theorem inequalities_8960 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (x - y) * sqrt (3 * x ^ 2 + y ^ 2) + (y - z) * sqrt (3 * y ^ 2 + z ^ 2) + (z - x) * sqrt (3 * z ^ 2 + x ^ 2) ≥ 0 := by

  have h1 : (x - y) * sqrt (3 * x ^ 2 + y ^ 2) ≥ x^2 - y^2 := by
    by_cases h2 : x ≥ y
    · -- x ≥ y, so x - y ≥ 0
      have h3 : sqrt (3 * x^2 + y^2) ≥ x + y := by
        have h4 : (x + y) ^ 2 ≤ 3 * x^2 + y^2 := by
          nlinarith [sq_nonneg (x - y)]
        have h5 : x + y ≤ sqrt (3 * x^2 + y^2) := by
          apply le_sqrt_of_sq_le
          nlinarith
        linarith
      have h3' : (x - y) * sqrt (3 * x^2 + y^2) ≥ (x - y) * (x + y) := by
        apply mul_le_mul_of_nonneg_left
        linarith
        nlinarith
      have h4 : (x - y) * (x + y) = x^2 - y^2 := by
        ring
      linarith [h4, h3']
    · -- y > x, so x - y < 0
      have h3 : sqrt (3 * x^2 + y^2) ≤ x + y := by
        have h4 : (x + y) ^ 2 ≥ 3 * x^2 + y^2 := by
          nlinarith [sq_nonneg (x - y)]
        have h5 : sqrt (3 * x^2 + y^2) ≤ x + y := by
          nlinarith [Real.sqrt_nonneg (3 * x^2 + y^2), Real.sq_sqrt (show 0 ≤ (3 * x^2 + y^2 : ℝ) by positivity)]
        linarith
      have h6 : (x - y) * sqrt (3 * x^2 + y^2) ≥ (x - y) * (x + y) := by
        apply mul_le_mul_of_nonpos_left
        linarith
        nlinarith
      have h7 : (x - y) * (x + y) = x^2 - y^2 := by
        ring
      linarith [h7, h6]

  have h2 : (y - z) * sqrt (3 * y ^ 2 + z ^ 2) ≥ y^2 - z^2 := by
    by_cases h2 : y ≥ z
    · -- y ≥ z, so y - z ≥ 0
      have h3 : sqrt (3 * y^2 + z^2) ≥ y + z := by
        have h4 : (y + z) ^ 2 ≤ 3 * y^2 + z^2 := by
          nlinarith [sq_nonneg (y - z)]
        have h5 : y + z ≤ sqrt (3 * y^2 + z^2) := by
          apply le_sqrt_of_sq_le
          nlinarith
        linarith
      have h3' : (y - z) * sqrt (3 * y^2 + z^2) ≥ (y - z) * (y + z) := by
        apply mul_le_mul_of_nonneg_left
        linarith
        nlinarith
      have h4 : (y - z) * (y + z) = y^2 - z^2 := by
        ring
      linarith [h4, h3']
    · -- z > y, so y - z < 0
      have h3 : sqrt (3 * y^2 + z^2) ≤ y + z := by
        have h4 : (y + z) ^ 2 ≥ 3 * y^2 + z^2 := by
          nlinarith [sq_nonneg (y - z)]
        have h5 : sqrt (3 * y^2 + z^2) ≤ y + z := by
          nlinarith [Real.sqrt_nonneg (3 * y^2 + z^2), Real.sq_sqrt (show 0 ≤ (3 * y^2 + z^2 : ℝ) by positivity)]
        linarith
      have h6 : (y - z) * sqrt (3 * y^2 + z^2) ≥ (y - z) * (y + z) := by
        apply mul_le_mul_of_nonpos_left
        linarith
        nlinarith
      have h7 : (y - z) * (y + z) = y^2 - z^2 := by
        ring
      linarith [h7, h6]

  have h3 : (z - x) * sqrt (3 * z ^ 2 + x ^ 2) ≥ z^2 - x^2 := by
    by_cases h4 : z ≥ x
    · -- z ≥ x, so z - x ≥ 0
      have h5 : sqrt (3 * z^2 + x^2) ≥ z + x := by
        have h6 : (z + x) ^ 2 ≤ 3 * z^2 + x^2 := by
          nlinarith [sq_nonneg (z - x)]
        have h7 : z + x ≤ sqrt (3 * z^2 + x^2) := by
          apply le_sqrt_of_sq_le
          nlinarith
        linarith
      have h5' : (z - x) * sqrt (3 * z^2 + x^2) ≥ (z - x) * (z + x) := by
        apply mul_le_mul_of_nonneg_left
        linarith
        nlinarith
      have h8 : (z - x) * (z + x) = z^2 - x^2 := by
        ring
      linarith [h8, h5']
    · -- x > z, so z - x < 0
      have h6 : sqrt (3 * z^2 + x^2) ≤ z + x := by
        have h7 : (z + x) ^ 2 ≥ 3 * z^2 + x^2 := by
          nlinarith [sq_nonneg (z - x)]
        have h8 : sqrt (3 * z^2 + x^2) ≤ z + x := by
          nlinarith [Real.sqrt_nonneg (3 * z^2 + x^2), Real.sq_sqrt (show 0 ≤ (3 * z^2 + x^2 : ℝ) by positivity)]
        linarith
      have h9 : (z - x) * sqrt (3 * z^2 + x^2) ≥ (z - x) * (z + x) := by
        apply mul_le_mul_of_nonpos_left
        linarith
        nlinarith
      have h10 : (z - x) * (z + x) = z^2 - x^2 := by
        ring
      linarith [h10, h9]

  linarith [h1, h2, h3]