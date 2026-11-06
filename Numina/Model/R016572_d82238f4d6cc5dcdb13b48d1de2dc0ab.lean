import Mathlib

theorem algebra_154285 {z : ℂ} (hz : z = 1 + Complex.I) :
    z = Real.sqrt 2 * (Complex.cos (Real.pi / 4) + Complex.I * Complex.sin (Real.pi / 4)) := by 
  rw [hz]
  have hcos : Complex.cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
    have h : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
    exact_mod_cast h
  have hsin : Complex.sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
    have h : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
    exact_mod_cast h
  rw [hcos, hsin]
  field_simp [Complex.ext_iff, mul_add, mul_comm]
  <;> ring_nf <;> norm_num [Real.sq_sqrt]