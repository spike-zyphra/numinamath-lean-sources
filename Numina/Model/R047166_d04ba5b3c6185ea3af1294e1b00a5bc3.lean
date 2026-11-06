import Mathlib

theorem algebra_154312 (a b : ℝ) (z : ℂ) (hz : z = Complex.exp a * Complex.exp (Complex.I * b)) :
    z = Complex.exp (a + Complex.I * b) := by
  rw [hz]
  have h1 : Complex.exp a * Complex.exp (Complex.I * b) = Complex.exp (a + Complex.I * b) := by 
    have h2 : a + Complex.I * b = (a : ℂ) + (Complex.I * b : ℂ) := by 
      simp
      <;> ring_nf
      <;> norm_num [Complex.ext_iff]
    rw [h2]
    rw [←Complex.exp_add]
  exact_mod_cast h1