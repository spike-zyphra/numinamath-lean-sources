import Mathlib

theorem algebra_148277 {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    ((1 - (x / y) ^ 2) * y ^ 2 * (x - y) ^ (-1 : ℝ)) / ((Real.sqrt x - Real.sqrt y) ^ 2 + Real.sqrt (4 * x * y)) = -1 := by
  have h0 : 0 < x * y := by
    nlinarith
  have h1 : Real.sqrt (4 * x * y) = 2 * Real.sqrt (x * y) := by
    have h2 : Real.sqrt (4 * x * y) = Real.sqrt (4 * (x * y)) := by ring_nf
    rw [h2]
    have h4 : Real.sqrt (4 * (x * y)) = Real.sqrt 4 * Real.sqrt (x * y) := by
      rw [Real.sqrt_mul (by positivity)]
    rw [h4]
    have h5 : Real.sqrt (4 : ℝ) = 2 := by
      rw [Real.sqrt_eq_cases]
      norm_num
    rw [h5]
  have h7 : Real.sqrt (x * y) = Real.sqrt x * Real.sqrt y := by
    rw [Real.sqrt_mul (by positivity)]
  have h8 : Real.sqrt (4 * x * y) = 2 * (Real.sqrt x * Real.sqrt y) := by
    rw [h1, h7]
  have h9 : (Real.sqrt x - Real.sqrt y) ^ 2 + Real.sqrt (4 * x * y) = x + y := by
    have h10 : (Real.sqrt x - Real.sqrt y) ^ 2 = x + y - 2 * (Real.sqrt x * Real.sqrt y) := by
      nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y, Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ y by linarith), Real.sqrt_le_sqrt (show x ≥ 0 by linarith), Real.sqrt_le_sqrt (show y ≥ 0 by linarith), mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]
    rw [h10, h8]
    nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y, Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ y by linarith), mul_pos hx hy, Real.sqrt_nonneg (x * y)]
  have h11 : ((1 - (x / y) ^ 2) * y ^ 2 * (x - y) ^ (-1 : ℝ)) = -(x + y) := by
    have h12 : (1 - (x / y) ^ 2) * y ^ 2 = y^2 - x^2 := by
      field_simp
      <;> nlinarith
    rw [h12]
    have h14 : y ^ 2 - x ^ 2 = (y - x) * (y + x) := by
      ring
    rw [h14]
    have h15 : x - y ≠ 0 := by
      intro h
      apply hxy
      linarith
    have h16 : (x - y : ℝ) ^ (-1 : ℝ) = (1 / (x - y)) := by
      simp [Real.rpow_neg_one]
    rw [h16]
    have h17 : (y - x) * (y + x) * (1 / (x - y)) = (y - x) * (y + x) / (x - y) := by
      field_simp [h15]
      <;> nlinarith
    rw [h17]
    have h18 : (y - x) * (y + x) / (x - y) = -(x + y) := by
      have h19 : x - y ≠ 0 := h15
      have h20 : y - x = -(x - y) := by linarith
      rw [h20]
      field_simp [h19]
      <;> nlinarith
    rw [h18]
  rw [h11, h9]
  have h10' : x + y ≠ 0 := by
    linarith
  field_simp [h10', show x - y ≠ 0 by
    intro h
    apply hxy
    linarith
  ]