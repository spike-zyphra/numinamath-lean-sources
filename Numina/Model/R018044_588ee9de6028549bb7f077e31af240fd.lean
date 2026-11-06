import Mathlib

theorem algebra_172353 {z : ℂ} (hz : z = ((4 - 3 * .I) ^ 2 * (-1 - Real.sqrt 3 * .I) ^ 10) / (1 + .I) ^ 12) :
    Complex.abs z = 400 := by
  rw [hz]
  have h1 : Complex.abs (((4 - 3 * Complex.I) ^ 2 * (-1 - Real.sqrt 3 * Complex.I) ^ 10) / (1 + Complex.I) ^ 12) =
    (Complex.abs ((4 - 3 * Complex.I) ^ 2 * (-1 - Real.sqrt 3 * Complex.I) ^ 10)) / (Complex.abs ((1 + Complex.I) ^ 12)) := by
    field_simp [Complex.abs]
    <;> norm_num [Complex.abs]
  rw [h1]
  have h2 : Complex.abs ((4 - 3 * Complex.I) ^ 2 * (-1 - Real.sqrt 3 * Complex.I) ^ 10) =
      Complex.abs ((4 - 3 * Complex.I) ^ 2) * Complex.abs ((-1 - Real.sqrt 3 * Complex.I) ^ 10) := by
    simp [Complex.abs, Complex.normSq]
  rw [h2]
  have h3 : Complex.abs ((4 - 3 * Complex.I) ^ 2) = Complex.abs (4 - 3 * Complex.I) ^ 2 := by
    simp [Complex.abs, Complex.normSq]
  have h4 : Complex.abs ((-1 - Real.sqrt 3 * Complex.I) ^ 10) = Complex.abs (-1 - Real.sqrt 3 * Complex.I) ^ 10 := by
    simp [Complex.abs, Complex.normSq]
  rw [h3, h4]
  have h5 : Complex.abs (4 - 3 * Complex.I) = 5 := by
    simp [Complex.abs, Complex.normSq, pow_two]
    ring_nf
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h6 : Complex.abs (-1 - Real.sqrt 3 * Complex.I) = 2 := by
    simp [Complex.abs, Complex.normSq, pow_two]
    have h7 : Real.sqrt ((-1 : ℝ) ^ 2 + (Real.sqrt 3) ^ 2) = 2 := by
      have h8 : ((-1 : ℝ) ^ 2 + (Real.sqrt 3) ^ 2) = (4 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      rw [h8]
      have h4 : Real.sqrt (4 : ℝ) = (2 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      linarith [h4]
    ring_nf at *
    norm_num at h7 ⊢
    <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  rw [h5, h6]
  have h7 : Complex.abs ((1 + Complex.I) ^ 12) = Complex.abs (1 + Complex.I) ^ 12 := by
    simp [Complex.abs, Complex.normSq]
  rw [h7]
  have h8 : Complex.abs (1 + Complex.I) = Real.sqrt 2 := by
    simp [Complex.abs, Complex.normSq]
    ring_nf
  rw [h8]
  have h9 : Real.sqrt 2 ^ 12 = (2 : ℝ) ^ 6 := by
    calc
      Real.sqrt 2 ^ 12 = (Real.sqrt 2 ^ 2) ^ 6 := by ring_nf
      _ = (2 : ℝ) ^ 6 := by
        rw [Real.sq_sqrt]
        all_goals norm_num
  rw [h9]
  all_goals norm_num
  all_goals norm_num