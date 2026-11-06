import Mathlib

theorem algebra_13538 : Complex.abs (3 + Real.sqrt 7 * .I)^3 = 64 := by
  have h1 : Complex.abs (3 + Real.sqrt 7 * Complex.I) = 4 := by 
    simp [Complex.abs, Complex.normSq] 
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
    <;> ring_nf <;> norm_num
  have h2 : Complex.abs (3 + Real.sqrt 7 * Complex.I)^3 = (Complex.abs (3 + Real.sqrt 7 * Complex.I)) ^ 3 := by 
    simp [Complex.abs_pow]
  rw [h2, h1]
  all_goals norm_num