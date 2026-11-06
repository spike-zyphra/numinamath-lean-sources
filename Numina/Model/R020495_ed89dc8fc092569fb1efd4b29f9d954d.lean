import Mathlib

theorem algebra_927 :
  {x : ℂ | x^2 - 2 * x + 2 = 0} ≠ {x : ℂ | x^2 + 2 * x + 2 = 0} := by
  have h1 : (1 + Complex.I : ℂ) ∈ {x : ℂ | x^2 - 2 * x + 2 = 0} := by
    simp [pow_two, Complex.ext_iff, Complex.I_mul_I]
    <;> norm_num 
  have h2 : (1 + Complex.I : ℂ) ∉ {x : ℂ | x^2 + 2 * x + 2 = 0} := by
    simp [pow_two, Complex.ext_iff, Complex.I_mul_I]
    <;> norm_num 
  intro h
  rw [h] at h1
  contradiction