import Mathlib

theorem inequalities_313941 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : x * y + y * z + z * x = 1) :
    5 / 2 ≤ 1 / (x + y) + 1 / (y + z) + 1 / (z + x) := by
  have h1 : x + y ≠ 0 := by
    by_contra h1
    have h2 : x * y + y * z + z * x = 0 := by
      have h3 : x + y = 0 := by linarith
      have h4 : x = 0 := by nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z)]
      have h5 : y = 0 := by nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z)]
      rw [h4, h5]
      nlinarith
    linarith
  have h2 : y + z ≠ 0 := by
    by_contra h2
    have h3 : x * y + y * z + z * x = 0 := by
      have h4 : y + z = 0 := by linarith
      have h5 : y = 0 := by nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z)]
      have h6 : z = 0 := by nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z)]
      rw [h5, h6]
      nlinarith
    linarith
  have h3 : z + x ≠ 0 := by
    by_contra h3
    have h4 : x * y + y * z + z * x = 0 := by
      have h5 : z + x = 0 := by linarith
      have h6 : z = 0 := by nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z)]
      have h7 : x = 0 := by nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z)]
      rw [h6, h7]
      nlinarith
    linarith
  have h4 : 0 < x + y := by
    by_contra h4
    push_neg at h4
    have h5 : x + y ≤ 0 := by linarith
    have h6 : x ≤ 0 := by nlinarith [show y ≥ 0 from hy]
    have h7 : y ≤ 0 := by nlinarith [show x ≥ 0 from hx]
    have h8 : x = 0 := by linarith [show x ≤ 0 from h6, show x ≥ 0 from hx]
    have h9 : y = 0 := by linarith [show y ≤ 0 from h7, show y ≥ 0 from hy]
    rw [h8, h9] at h
    nlinarith [show z ≥ 0 from hz]
  have h5 : 0 < y + z := by
    by_contra h5
    push_neg at h5
    have h6 : y + z ≤ 0 := by linarith
    have h7 : y ≤ 0 := by nlinarith [show z ≥ 0 from hz]
    have h8 : z ≤ 0 := by nlinarith [show y ≥ 0 from hy]
    have h9 : y = 0 := by linarith [show y ≤ 0 from h7, show y ≥ 0 from hy]
    have h10 : z = 0 := by linarith [show z ≤ 0 from h8, show z ≥ 0 from hz]
    rw [h9, h10] at h
    nlinarith [show x ≥ 0 from hx]
  have h6 : 0 < z + x := by
    by_contra h6
    push_neg at h6
    have h7 : z + x ≤ 0 := by linarith
    have h8 : z ≤ 0 := by nlinarith [show x ≥ 0 from hx]
    have h9 : x ≤ 0 := by nlinarith [show z ≥ 0 from hz]
    have h10 : z = 0 := by linarith [show z ≤ 0 from h8, show z ≥ 0 from hz]
    have h11 : x = 0 := by linarith [show x ≤ 0 from h9, show x ≥ 0 from hx]
    rw [h11, h10] at h
    nlinarith [show y ≥ 0 from hy]
  have h7 : 1 / (x + y) + 1 / (y + z) + 1 / (z + x) - 5 / 2 ≥ 0 := by
    have h8 : (1 / (x + y) + 1 / (y + z) + 1 / (z + x) - 5 / 2) =
        (2 * (y + z) * (z + x) + 2 * (x + y) * (z + x) + 2 * (x + y) * (y + z) - 5 * (x + y) * (y + z) * (z + x)) / (2 * (x + y) * (y + z) * (z + x)) := by
      field_simp
      ring
    rw [h8] at *
    have h9 : 2 * (y + z) * (z + x) + 2 * (x + y) * (z + x) + 2 * (x + y) * (y + z) - 5 * (x + y) * (y + z) * (z + x) ≥ 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        sq_nonneg (x + y + z - 2), sq_nonneg (x * y + y * z + z * x - 1), mul_nonneg hx hy, mul_nonneg hy hz, mul_nonneg hz hx, mul_nonneg (show (0 : ℝ) ≤ x * y by nlinarith) (show (0 : ℝ) ≤ y * z by nlinarith), mul_nonneg (show (0 : ℝ) ≤ y * z by nlinarith) (show (0 : ℝ) ≤ z * x by nlinarith), mul_nonneg (show (0 : ℝ) ≤ z * x by nlinarith) (show (0 : ℝ) ≤ x * y by nlinarith)]
    have h10 : (2 * (y + z) * (z + x) + 2 * (x + y) * (z + x) + 2 * (x + y) * (y + z) - 5 * (x + y) * (y + z) * (z + x)) / (2 * (x + y) * (y + z) * (z + x)) ≥ 0 := by
      apply div_nonneg
      linarith
      positivity
    linarith
  linarith