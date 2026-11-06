import Mathlib

open Real

theorem inequalities_47934 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hsum : x + y + z = 1) :
    sqrt (x * y + z) + sqrt (y * z + x) + sqrt (z * x + y) ≥
    1 + sqrt (x * y) + sqrt (y * z) + sqrt (z * x) := by

  have h1 : sqrt (x * y + z) ≥ z + sqrt (x * y) := by
    have h2 : 0 < x * y := mul_pos hx hy
    have h3 : 0 < z := hz
    have h4 : (z + sqrt (x * y)) ^ 2 ≤ x * y + z := by
      have h5 : (z + sqrt (x * y)) ^ 2 = z ^ 2 + x * y + 2 * z * sqrt (x * y) := by
        have h6 : sqrt (x * y) ^ 2 = x * y := by
          rw [Real.sq_sqrt]
          positivity
        nlinarith [h6, Real.sqrt_nonneg (x * y)]
      rw [h5] at *
      have h7 : x + y = 1 - z := by linarith
      have h8 : x + y ≥ 2 * sqrt (x * y) := by
        have h9 : (sqrt (x) - sqrt (y)) ^ 2 ≥ 0 := by nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y]
        have h10 : sqrt (x) ^ 2 = x := Real.sq_sqrt (by linarith)
        have h11 : sqrt (y) ^ 2 = y := Real.sq_sqrt (by linarith)
        have h12 : sqrt (x * y) = sqrt (x) * sqrt (y) := by
          rw [Real.sqrt_mul (by linarith)]
        nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y, h9, h10, h11, h12, sq_nonneg (sqrt (x) - sqrt (y)), sq_nonneg (x - y), mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]
      have h13 : 1 - z ≥ 2 * sqrt (x * y) := by
        have h14 : 1 - z = x + y := by nlinarith
        nlinarith [h8, h14]
      nlinarith [Real.sqrt_nonneg (x * y), mul_nonneg (show (0 : ℝ) ≤ z by linarith) (show (0 : ℝ) ≤ sqrt (x * y) by positivity), h13, Real.sqrt_nonneg (x * y)]
    have h5 : z + sqrt (x * y) ≥ 0 := by positivity
    have h6 : sqrt (x * y + z) ≥ z + sqrt (x * y) := by
      have h11 : (z + sqrt (x * y)) ^ 2 ≤ x * y + z := h4
      have h12 : z + sqrt (x * y) ≥ 0 := h5
      have h7 : sqrt (x * y + z) ≥ z + sqrt (x * y) := by
        apply Real.le_sqrt_of_sq_le
        nlinarith [h11, h12]
      exact h7
    exact h6

  have h2 : sqrt (y * z + x) ≥ x + sqrt (y * z) := by
    have h2 : 0 < y * z := mul_pos hy hz
    have h3 : 0 < x := hx
    have h4 : (x + sqrt (y * z)) ^ 2 ≤ y * z + x := by
      have h5 : (x + sqrt (y * z)) ^ 2 = x ^ 2 + y * z + 2 * x * sqrt (y * z) := by
        have h6 : sqrt (y * z) ^ 2 = y * z := by
          rw [Real.sq_sqrt]
          positivity
        nlinarith [h6, Real.sqrt_nonneg (y * z)]
      rw [h5] at *
      have h7 : y + z = 1 - x := by linarith
      have h8 : y + z ≥ 2 * sqrt (y * z) := by
        have h9 : (sqrt (y) - sqrt (z)) ^ 2 ≥ 0 := by nlinarith [Real.sqrt_nonneg y, Real.sqrt_nonneg z]
        have h10 : sqrt (y) ^ 2 = y := Real.sq_sqrt (by linarith)
        have h11 : sqrt (z) ^ 2 = z := Real.sq_sqrt (by linarith)
        have h12 : sqrt (y * z) = sqrt (y) * sqrt (z) := by
          rw [Real.sqrt_mul (by linarith)]
        nlinarith [Real.sqrt_nonneg y, Real.sqrt_nonneg z, h9, h10, h11, h12, sq_nonneg (sqrt (y) - sqrt (z)), sq_nonneg (y - z), mul_nonneg (Real.sqrt_nonneg y) (Real.sqrt_nonneg z)]
      have h13 : 1 - x ≥ 2 * sqrt (y * z) := by
        have h14 : 1 - x = y + z := by nlinarith
        nlinarith [h8, h14]
      nlinarith [Real.sqrt_nonneg (y * z), mul_nonneg (show (0 : ℝ) ≤ x by linarith) (show (0 : ℝ) ≤ sqrt (y * z) by positivity), h13, Real.sqrt_nonneg (y * z)]
    have h5 : x + sqrt (y * z) ≥ 0 := by positivity
    have h6 : sqrt (y * z + x) ≥ x + sqrt (y * z) := by
      have h11 : (x + sqrt (y * z)) ^ 2 ≤ y * z + x := h4
      have h12 : x + sqrt (y * z) ≥ 0 := h5
      have h7 : sqrt (y * z + x) ≥ x + sqrt (y * z) := by
        apply Real.le_sqrt_of_sq_le
        nlinarith [h11, h12]
      exact h7
    exact h6

  have h3 : sqrt (z * x + y) ≥ y + sqrt (z * x) := by
    have h2 : 0 < z * x := mul_pos hz hx
    have h3 : 0 < y := hy
    have h4 : (y + sqrt (z * x)) ^ 2 ≤ z * x + y := by
      have h5 : (y + sqrt (z * x)) ^ 2 = y ^ 2 + z * x + 2 * y * sqrt (z * x) := by
        have h6 : sqrt (z * x) ^ 2 = z * x := by
          rw [Real.sq_sqrt]
          positivity
        nlinarith [h6, Real.sqrt_nonneg (z * x)]
      rw [h5] at *
      have h7 : z + x = 1 - y := by linarith
      have h8 : z + x ≥ 2 * sqrt (z * x) := by
        have h9 : (sqrt (z) - sqrt (x)) ^ 2 ≥ 0 := by nlinarith [Real.sqrt_nonneg z, Real.sqrt_nonneg x]
        have h10 : sqrt (z) ^ 2 = z := Real.sq_sqrt (by linarith)
        have h11 : sqrt (x) ^ 2 = x := Real.sq_sqrt (by linarith)
        have h12 : sqrt (z * x) = sqrt (z) * sqrt (x) := by
          rw [Real.sqrt_mul (by linarith)]
        nlinarith [Real.sqrt_nonneg z, Real.sqrt_nonneg x, h9, h10, h11, h12, sq_nonneg (sqrt (z) - sqrt (x)), sq_nonneg (z - x), mul_nonneg (Real.sqrt_nonneg z) (Real.sqrt_nonneg x)]
      have h13 : 1 - y ≥ 2 * sqrt (z * x) := by
        have h14 : 1 - y = z + x := by nlinarith
        nlinarith [h8, h14]
      nlinarith [Real.sqrt_nonneg (z * x), mul_nonneg (show (0 : ℝ) ≤ y by linarith) (show (0 : ℝ) ≤ sqrt (z * x) by positivity), h13, Real.sqrt_nonneg (z * x)]
    have h5 : y + sqrt (z * x) ≥ 0 := by positivity
    have h6 : sqrt (z * x + y) ≥ y + sqrt (z * x) := by
      have h11 : (y + sqrt (z * x)) ^ 2 ≤ z * x + y := h4
      have h12 : y + sqrt (z * x) ≥ 0 := h5
      have h7 : sqrt (z * x + y) ≥ y + sqrt (z * x) := by
        apply Real.le_sqrt_of_sq_le
        nlinarith [h11, h12]
      exact h7
    exact h6

  have h4 : sqrt (x * y + z) + sqrt (y * z + x) + sqrt (z * x + y) ≥ (z + sqrt (x * y)) + (x + sqrt (y * z)) + (y + sqrt (z * x)) := by
    linarith [h1, h2, h3]

  have h5 : (z + sqrt (x * y)) + (x + sqrt (y * z)) + (y + sqrt (z * x)) = (x + y + z) + (sqrt (x * y) + sqrt (y * z) + sqrt (z * x)) := by ring

  have h7 : sqrt (x * y + z) + sqrt (y * z + x) + sqrt (z * x + y) ≥ 1 + sqrt (x * y) + sqrt (y * z) + sqrt (z * x) := by
    nlinarith [h4, h5, hsum]

  exact h7