import Mathlib

theorem algebra_14860 : Complex.abs (4 * Real.sqrt 2 - 4 * .I) * Complex.abs (Real.sqrt 3 + 3 * .I) = 24 := by
  have h11 : Complex.abs (4 * Real.sqrt 2 - 4 * Complex.I) = Real.sqrt ((4 * Real.sqrt 2)^2 + (-4 : ℝ) ^ 2) := by
    simp [Complex.abs, Complex.normSq, mul_pow]
    <;> ring_nf
    <;> simp [Complex.I_sq]
    <;> ring_nf
  have h12 : (4 * Real.sqrt 2) ^ 2 + (-4 : ℝ) ^ 2 = (48 : ℝ) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
  have h21 : Complex.abs (Real.sqrt 3 + 3 * Complex.I) = Real.sqrt ((Real.sqrt 3)^2 + (3 : ℝ) ^ 2) := by
    simp [Complex.abs, Complex.normSq, mul_pow]
    <;> ring_nf
    <;> simp [Complex.I_sq]
    <;> ring_nf
  have h22 : (Real.sqrt 3) ^ 2 + (3 : ℝ) ^ 2 = (12 : ℝ) := by
    have h3sq : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith [h3sq]
  have h23 : Real.sqrt ((4 * Real.sqrt 2) ^ 2 + (-4 : ℝ) ^ 2) = Real.sqrt 48 := by
    rw [h12]
  have h24 : Real.sqrt ((Real.sqrt 3) ^ 2 + (3 : ℝ) ^ 2) = Real.sqrt 12 := by
    rw [h22]
  rw [h11, h21]
  rw [h23, h24]
  have h3 : Real.sqrt 48 * Real.sqrt 12 = (24 : ℝ) := by
    calc
      Real.sqrt 48 * Real.sqrt 12 = Real.sqrt (48 * 12) := by
        rw [← Real.sqrt_mul (by norm_num)]
      _ = Real.sqrt (576 : ℝ) := by norm_num
      _ = (24 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  exact h3