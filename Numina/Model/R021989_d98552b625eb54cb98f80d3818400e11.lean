import Mathlib

theorem algebra_151766 {z : ℂ} (hz : Complex.abs z * (3 * z + 2 * .I) = 2 * (.I * z - 6)) :
    Complex.abs z = 2 := by
  have h1 : Complex.abs (Complex.abs z * (3 * z + 2 * Complex.I)) = Complex.abs (2 * (Complex.I * z - 6)) := by
    rw [hz]
  have h2 : Complex.abs (Complex.abs z * (3 * z + 2 * Complex.I)) = Complex.abs z * Complex.abs (3 * z + 2 * Complex.I) := by
    simp [Complex.abs, Complex.normSq]
  have h3 : Complex.abs (2 * (Complex.I * z - 6)) = 2 * Complex.abs (Complex.I * z - 6) := by
    simp [Complex.abs, Complex.normSq]
  rw [h2, h3] at h1
  have eq1 : Complex.abs z * Complex.abs (3 * z + 2 * Complex.I) = 2 * Complex.abs (Complex.I * z - 6) := by
    simpa using h1
  have eq2 : Complex.abs z = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    all_goals
      ring_nf 
  have eq3 : Complex.abs (3 * z + 2 * Complex.I) = Real.sqrt ((3 * z.re) ^ 2 + (3 * z.im + 2) ^ 2) := by
    simp [Complex.abs, Complex.normSq, mul_add, pow_two, Complex.re, Complex.im]
    all_goals
      ring_nf 
  have eq4 : Complex.abs (Complex.I * z - 6) = Real.sqrt ((-z.im - 6) ^ 2 + z.re ^ 2) := by
    simp [Complex.abs, Complex.normSq, Complex.I_mul_I, mul_add, pow_two, Complex.re, Complex.im]
    all_goals
      ring_nf 
  rw [eq2, eq3, eq4] at eq1
  have eq5 : (Real.sqrt (z.re ^ 2 + z.im ^ 2) * Real.sqrt ((3 * z.re) ^ 2 + (3 * z.im + 2) ^ 2)) ^ 2 = (2 * Real.sqrt ((-z.im - 6) ^ 2 + z.re ^ 2) ) ^ 2 := by
    have h7 : Real.sqrt (z.re ^ 2 + z.im ^ 2) * Real.sqrt ((3 * z.re) ^ 2 + (3 * z.im + 2) ^ 2) = 2 * Real.sqrt ((-z.im - 6) ^ 2 + z.re ^ 2) := by
      linarith [eq1]
    rw [h7]
  have eq6 : (Real.sqrt (z.re ^ 2 + z.im ^ 2) * Real.sqrt ((3 * z.re) ^ 2 + (3 * z.im + 2) ^ 2)) ^ 2 =
      (Real.sqrt (z.re ^ 2 + z.im ^ 2)) ^ 2 * (Real.sqrt ((3 * z.re) ^ 2 + (3 * z.im + 2) ^ 2)) ^ 2 := by
    ring_nf
  rw [eq6] at eq5
  have eq7 : (Real.sqrt (z.re ^ 2 + z.im ^ 2)) ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  have eq8 : (Real.sqrt ((3 * z.re) ^ 2 + (3 * z.im + 2) ^ 2)) ^ 2 = (3 * z.re) ^ 2 + (3 * z.im + 2) ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  have eq9 : (2 * Real.sqrt ((-z.im - 6) ^ 2 + z.re ^ 2) ) ^ 2 = 4 * ((-z.im - 6) ^ 2 + z.re ^ 2) := by
    calc
      (2 * Real.sqrt ((-z.im - 6) ^ 2 + z.re ^ 2) ) ^ 2 = 4 * (Real.sqrt ((-z.im - 6) ^ 2 + z.re ^ 2) ^ 2) := by
        ring_nf
      _ = 4 * ((-z.im - 6) ^ 2 + z.re ^ 2) := by
        rw [Real.sq_sqrt]
        positivity
  rw [eq7, eq8, eq9] at eq5
  have eq11 : z.re ^ 2 + z.im ^ 2 = 4 := by
    nlinarith [sq_nonneg (z.re ^ 2 + z.im ^ 2 - 4), sq_nonneg (3 * z.re ^ 2 + 4 * z.im ^ 2), sq_nonneg (z.im + 2), sq_nonneg (z.re ^ 2 + z.im ^ 2), sq_nonneg (z.re ^ 2 - 4), sq_nonneg (z.im ^ 2 - 0)]
  have eq12 : Complex.abs z = 2 := by
    rw [eq2]
    have h3 : Real.sqrt (z.re ^ 2 + z.im ^ 2) = 2 := by
      have h4 : z.re ^ 2 + z.im ^ 2 = 4 := eq11
      have h5 : Real.sqrt (z.re ^ 2 + z.im ^ 2) = Real.sqrt 4 := by
        rw [show z.re ^ 2 + z.im ^ 2 = (4 : ℝ) by linarith]
      have h6 : Real.sqrt (4 : ℝ) = 2 := Real.sqrt_eq_cases.mpr (by norm_num)
      rw [h6] at h5
      linarith
    linarith
  exact eq12