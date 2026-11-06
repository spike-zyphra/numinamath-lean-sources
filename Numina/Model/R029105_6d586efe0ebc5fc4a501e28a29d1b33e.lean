import Mathlib

theorem algebra_154366 {z : ℂ} (hz : z = -Real.sqrt 3 + Complex.I) :
    z^6 = -64 := by
  rw [hz]
  have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h2 : ( -Real.sqrt 3 + Complex.I ) ^ 3 = 8 * Complex.I := by
    simp [pow_three, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, h1]
    ring_nf
    <;> norm_num [h1, pow_three, pow_succ]

  have h3 : ( -Real.sqrt 3 + Complex.I ) ^ 6 = ( ( -Real.sqrt 3 + Complex.I ) ^ 3 ) ^ 2 := by ring
  rw [h3]
  rw [h2]
  simp [pow_two, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  <;> norm_num