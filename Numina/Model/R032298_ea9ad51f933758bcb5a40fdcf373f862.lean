import Mathlib


open Complex


theorem algebra_111013 {z : ℂ} (hz : z = (4 - 3 * Complex.I)^2 * (-1 - Real.sqrt 3 * Complex.I)^10 / (1 + Complex.I)^12) :
    Complex.abs z = 400 := by
  rw [hz]
  have h1 : Complex.abs ((4 - 3 * Complex.I) ^ 2 * (-1 - Real.sqrt 3 * Complex.I) ^ 10 / (1 + Complex.I) ^ 12) =
      Complex.abs ((4 - 3 * Complex.I) ^ 2 * (-1 - Real.sqrt 3 * Complex.I) ^ 10) / Complex.abs ((1 + Complex.I) ^ 12) := by
    field_simp [Complex.abs]
  have h2 : Complex.abs ((4 - 3 * Complex.I) ^ 2 * (-1 - Real.sqrt 3 * Complex.I) ^ 10) =
      Complex.abs ((4 - 3 * Complex.I) ^ 2) * Complex.abs ((-1 - Real.sqrt 3 * Complex.I) ^ 10) := by
    simp [Complex.abs, Complex.normSq]
  have h3 : Complex.abs ((4 - 3 * Complex.I) ^ 2) = Complex.abs (4 - 3 * Complex.I) ^ 2 := by
    simp [Complex.abs, Complex.normSq]
  have h4 : Complex.abs (4 - 3 * Complex.I) = (5 : ℝ) := by
    simp [Complex.abs, Complex.normSq]
    ring_nf
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h5 : Complex.abs ((-1 - Real.sqrt 3 * Complex.I) ^ 10) = Complex.abs (-1 - Real.sqrt 3 * Complex.I) ^ 10 := by
    simp [Complex.abs, Complex.normSq]
  have h6 : Complex.abs (-1 - Real.sqrt 3 * Complex.I) = (2 : ℝ) := by
    simp [Complex.abs, Complex.normSq]
    ring_nf
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h7 : Complex.abs ((1 + Complex.I) ^ 12) = Complex.abs (1 + Complex.I) ^ 12 := by
    simp [Complex.abs, Complex.normSq]
  have h8 : Complex.abs (1 + Complex.I) = Real.sqrt 2 := by
    simp [Complex.abs, Complex.normSq]
    all_goals ring_nf
  rw [h1]
  rw [h2]
  rw [h3, h5, h7]
  rw [h4, h6, h8]
  have h12 : Real.sqrt 2 ≥ 0 := by positivity
  have h13 : (Real.sqrt 2 : ℝ) ^ 12 = (64 : ℝ) := by
    have h5 : (Real.sqrt 2 : ℝ) ^ 2 = (2 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
    calc
      (Real.sqrt 2 : ℝ) ^ 12 = ((Real.sqrt 2 : ℝ) ^ 2) ^ 6 := by ring
      _ = (2 : ℝ) ^ 6 := by rw [h5]
      _ = (64 : ℝ) := by norm_num
  field_simp [h13]
  all_goals norm_num