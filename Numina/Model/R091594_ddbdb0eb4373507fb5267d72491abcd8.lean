import Mathlib

theorem algebra_239357 {z : ℂ} (hz : z = (2 + 3 * .I)^2011 / (2 - 3 * .I)^2009) :
    Complex.abs z = 13 := by
  rw [hz]
  have h1 : Complex.abs ((2 + 3 * Complex.I) ^ 2011 / (2 - 3 * Complex.I) ^ 2009) =
      Complex.abs ((2 + 3 * Complex.I) ^ 2011) / Complex.abs ((2 - 3 * Complex.I) ^ 2009) := by
    field_simp [Complex.abs]
    <;> norm_num [Complex.abs]
  rw [h1]
  have h2 : Complex.abs ((2 + 3 * Complex.I) ^ 2011) = (Complex.abs (2 + 3 * Complex.I)) ^ 2011 := by
    simp [Complex.abs_pow]
  have h3 : Complex.abs ((2 - 3 * Complex.I) ^ 2009) = (Complex.abs (2 - 3 * Complex.I)) ^ 2009 := by
    simp [Complex.abs_pow]
  rw [h2, h3]
  have h4 : Complex.abs (2 + 3 * Complex.I) = Real.sqrt 13 := by
    simp [Complex.abs, Complex.normSq]
    all_goals norm_num [Complex.normSq]
    <;> ring_nf <;> norm_num
  have h5 : Complex.abs (2 - 3 * Complex.I) = Real.sqrt 13 := by
    simp [Complex.abs, Complex.normSq]
    all_goals norm_num [Complex.normSq]
    <;> ring_nf <;> norm_num
  rw [h4, h5]
  have h6 : ((Real.sqrt 13 : ℝ) : ℝ) ^ 2011 / ((Real.sqrt 13 : ℝ) : ℝ) ^ 2009 = 13 := by
    have h7 : ((Real.sqrt 13 : ℝ) : ℝ) ^ 2011 = ((Real.sqrt 13 : ℝ) ^ 2009) * ((Real.sqrt 13 : ℝ) ^ 2) := by
      ring_nf
    rw [h7]
    field_simp
    <;> norm_num [Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)]
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 13 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)]
  norm_num [h6]
  <;> norm_num [Real.sqrt_pos.mpr (show (0 : ℝ) < 13 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)]