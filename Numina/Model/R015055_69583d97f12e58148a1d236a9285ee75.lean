import Mathlib

theorem algebra_160257 (x : ℝ) (hx : x ≥ 2) :
    1 / (Real.sqrt x + Real.sqrt (x - 2)) + 1 / (Real.sqrt (x + 2) + Real.sqrt x) = 1 / 4 ↔
    x = 257 / 16 := by
  constructor
  · -- Assume the equation holds, prove x = 257/16
    intro h
    have h1 : Real.sqrt x + Real.sqrt (x - 2) ≠ 0 := by
      by_contra h1
      have h2 : Real.sqrt x ≥ 0 := Real.sqrt_nonneg x
      have h3 : Real.sqrt (x - 2) ≥ 0 := Real.sqrt_nonneg (x - 2)
      have h4 : Real.sqrt x = 0 := by linarith [h1, h2, h3]
      have h5 : x = 0 := by
        rw [Real.sqrt_eq_zero (by linarith)] at h4
        linarith
      linarith
    have h2 : Real.sqrt (x + 2) + Real.sqrt x ≠ 0 := by
      by_contra h2
      have h3 : Real.sqrt (x + 2) ≥ 0 := Real.sqrt_nonneg (x + 2)
      have h4 : Real.sqrt x ≥ 0 := Real.sqrt_nonneg x
      have h5 : Real.sqrt (x + 2) = 0 := by linarith [h2, h3, h4]
      have h6 : x + 2 = 0 := by
        rw [Real.sqrt_eq_zero (by linarith)] at h5
        linarith
      linarith
    have eq1 : 1 / (Real.sqrt x + Real.sqrt (x - 2)) = (Real.sqrt x - Real.sqrt (x - 2)) / 2 := by
      have h6 : Real.sqrt x + Real.sqrt (x - 2) ≠ 0 := h1
      field_simp [h6]
      <;> nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg (x - 2), Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ x - 2 by linarith), mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg (x - 2))]
    have eq2 : 1 / (Real.sqrt (x + 2) + Real.sqrt x) = (Real.sqrt (x + 2) - Real.sqrt x) / 2 := by
      have h7 : Real.sqrt (x + 2) + Real.sqrt x ≠ 0 := h2
      field_simp [h7]
      <;> nlinarith [Real.sqrt_nonneg (x + 2), Real.sqrt_nonneg x, Real.sq_sqrt (show (0 : ℝ) ≤ x + 2 by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), mul_nonneg (Real.sqrt_nonneg (x + 2)) (Real.sqrt_nonneg x)]
    rw [eq1, eq2] at h
    have h3 : Real.sqrt (x + 2) - Real.sqrt (x - 2) = 1 / 2 := by
      linarith
    have h4 : Real.sqrt (x + 2) = Real.sqrt (x - 2) + 1 / 2 := by
      linarith
    have h5 : Real.sqrt (x + 2) ^ 2 = (Real.sqrt (x - 2) + 1 / 2) ^ 2 := by
      rw [h4]
    have h6 : Real.sqrt (x + 2) ^ 2 = x + 2 := by
      rw [Real.sq_sqrt]
      linarith
    have h7 : Real.sqrt (x - 2) ^ 2 = x - 2 := by
      rw [Real.sq_sqrt]
      linarith
    have h8 : Real.sqrt (x - 2) = 15 / 4 := by
      nlinarith [Real.sqrt_nonneg (x + 2), Real.sqrt_nonneg (x - 2), h6, h7, Real.sqrt_nonneg (x - 2)]
    have h9 : x - 2 = (225 / 16 : ℝ) := by
      calc
        x - 2 = (Real.sqrt (x - 2)) ^ 2 := by
          rw [Real.sq_sqrt]
          linarith
        _ = (15 / 4) ^ 2 := by
          rw [h8]
        _ = (225 / 16 : ℝ) := by
          norm_num
    have h10 : x = 257 / 16 := by
      linarith
    linarith
  · -- Assume x = 257/16, prove the equation
    intro h
    rw [h]
    have h1 : Real.sqrt (257 / 16 : ℝ) = Real.sqrt 257 / 4 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf
      <;> norm_num
    have h2 : Real.sqrt ((257 / 16 : ℝ) - 2) = (15 / 4 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h3 : Real.sqrt ((257 / 16 : ℝ) + 2) = (17 / 4 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h2, h3]
    field_simp
    <;> ring_nf
    <;> norm_num
    <;> nlinarith