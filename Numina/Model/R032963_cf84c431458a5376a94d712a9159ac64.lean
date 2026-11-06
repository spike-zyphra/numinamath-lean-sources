import Mathlib

theorem algebra_248779 (n : ℕ) :
    ((1 + Complex.I) / Real.sqrt 2) ^ (n + 4) +
    ((1 - Complex.I) / Real.sqrt 2) ^ (n + 4) +
    ((1 + Complex.I) / Real.sqrt 2) ^ n +
    ((1 - Complex.I) / Real.sqrt 2) ^ n = 0 := by

  have h1 : ((1 + Complex.I) / Real.sqrt 2) ^ 2 = Complex.I := by
    simp [pow_two, Complex.ext_iff, Complex.I_mul_I, Real.sqrt_sq]
    <;> ring_nf <;> norm_num

  have h2 : ((1 - Complex.I) / Real.sqrt 2) ^ 2 = -Complex.I := by
    simp [pow_two, Complex.ext_iff, Complex.I_mul_I, Real.sqrt_sq]
    <;> ring_nf <;> norm_num

  have h3 : ((1 + Complex.I) / Real.sqrt 2) ^ 4 = -1 := by
    calc
      ((1 + Complex.I) / Real.sqrt 2) ^ 4 = (((1 + Complex.I) / Real.sqrt 2) ^ 2) ^ 2 := by ring
      _ = (Complex.I) ^ 2 := by rw [h1]
      _ = -1 := by simp [Complex.I_sq]

  have h4 : ((1 - Complex.I) / Real.sqrt 2) ^ 4 = -1 := by
    calc
      ((1 - Complex.I) / Real.sqrt 2) ^ 4 = (((1 - Complex.I) / Real.sqrt 2) ^ 2) ^ 2 := by ring
      _ = (-Complex.I) ^ 2 := by rw [h2]
      _ = -1 := by simp [Complex.I_sq]

  have eq1 : ((1 + Complex.I) / Real.sqrt 2) ^ (n + 4) = - ((1 + Complex.I) / Real.sqrt 2) ^ n := by 
    calc
      ((1 + Complex.I) / Real.sqrt 2) ^ (n + 4) = ((1 + Complex.I) / Real.sqrt 2) ^ n * ((1 + Complex.I) / Real.sqrt 2) ^ 4 := by 
        ring_nf
      _ = ((1 + Complex.I) / Real.sqrt 2) ^ n * (-1) := by 
        rw [h3]
      _ = - ((1 + Complex.I) / Real.sqrt 2) ^ n := by 
        ring

  have eq2 : ((1 - Complex.I) / Real.sqrt 2) ^ (n + 4) = - ((1 - Complex.I) / Real.sqrt 2) ^ n := by
    calc
      ((1 - Complex.I) / Real.sqrt 2) ^ (n + 4) = ((1 - Complex.I) / Real.sqrt 2) ^ n * ((1 - Complex.I) / Real.sqrt 2) ^ 4 := by
        ring_nf
      _ = ((1 - Complex.I) / Real.sqrt 2) ^ n * (-1) := by 
        rw [h4]
      _ = - ((1 - Complex.I) / Real.sqrt 2) ^ n := by 
        ring

  rw [eq1, eq2]
  ring