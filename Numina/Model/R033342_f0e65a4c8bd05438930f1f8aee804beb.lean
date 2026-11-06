import Mathlib

theorem algebra_22105 {z : ℂ} (hz : Complex.abs z = 5) :
    Complex.abs (z.1 - z.2 * .I)^2 = 25 := by
  have h1 : Complex.abs (z.1 - z.2 * Complex.I) = Complex.abs z := by
    simp [Complex.abs, Complex.normSq]
    <;> ring
  calc
    Complex.abs (z.1 - z.2 * Complex.I)^2 = (Complex.abs (z.1 - z.2 * Complex.I)) ^ 2 := by
      simp [Complex.abs_pow]
    _ = (Complex.abs z) ^ 2 := by
      rw [h1]
    _ = (5 : ℝ) ^ 2 := by
      rw [hz]
    _ = (25 : ℝ) := by
      norm_num