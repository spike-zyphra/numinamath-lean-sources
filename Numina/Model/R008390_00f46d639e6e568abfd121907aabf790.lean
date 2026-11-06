import Mathlib

theorem algebra_9318 {a : ℝ} {z : ℂ} (hz : z = (a ^ 2 - 3 * a + 2) + (a - 2) * .I)
    (hzre : z.re = 0) (hzim : z.im ≠ 0) :
    a = 1 := by
  have h1 : z.re = a ^ 2 - 3 * a + 2 := by
    simp [hz, pow_two, Complex.add_re, Complex.ofReal_re, Complex.I_re, mul_comm]
    <;> ring
  have h4 : z.im = a - 2 := by
    simp [hz, pow_two, Complex.add_im, Complex.ofReal_im, Complex.I_im, mul_comm]
    <;> ring
  rw [h1] at hzre
  have h2 : a ^ 2 - 3 * a + 2 = 0 := by 
    linarith
  have h3 : (a - 1) * (a - 2) = 0 := by 
    nlinarith
  cases' (mul_eq_zero.mp h3) with ha1 ha2
  · 
    linarith
  · 
    have h5 : a - 2 = 0 := by
      linarith
    rw [h4] at hzim
    rw [h5] at hzim
    norm_num at hzim