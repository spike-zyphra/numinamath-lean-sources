import Mathlib

open Complex

theorem algebra_15278 : {z : ℂ | 2 - I * z = -1 + 3 * I * z} = {-3/4 * I} := by
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume $z$ is a solution; prove $z = -\frac{3}{4}i$
    intro h
    have eq1 := congr_arg Complex.re h
    have eq2 := congr_arg Complex.im h
    simp [Complex.add_re, Complex.ofReal_re, Complex.I_re, Complex.mul_re, 
          Complex.mul_im, Complex.ofReal_im, Complex.I_im] at eq1 eq2
    have h1 : z.re = 0 := by
      linarith
    have h2 : z.im = -3 / 4 := by
      linarith
    simp [Complex.ext_iff, h1, h2]
    all_goals norm_num
  · -- Assume $z = -\frac{3}{4}i$; prove it's a solution
    intro h
    rw [h]
    simp [Complex.ext_iff, Complex.add_re, Complex.ofReal_re, Complex.I_re, 
          Complex.I_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_im]
    all_goals norm_num