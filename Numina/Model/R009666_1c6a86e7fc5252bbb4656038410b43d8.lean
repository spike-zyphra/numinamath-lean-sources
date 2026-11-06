import Mathlib

theorem algebra_8984
    {a : ℝ}
    (z : ℂ)
    (hz : z = a ^ 2 + a - 2 + (a ^ 2 - 3 * a + 2) * Complex.I)
    (h : z.re = 0 ∧ z.im ≠ 0) : a = -2 := by

  have h1 : z.re = a ^ 2 + a - 2 := by
    simp [hz, pow_two, Complex.add_re, Complex.ofReal_re, Complex.I_re, Complex.zero_re]
    <;> ring

  have h2 : z.im = a ^ 2 - 3 * a + 2 := by
    simp [hz, pow_two, Complex.add_im, Complex.ofReal_im, Complex.I_im, Complex.zero_im]
    <;> ring

  rw [h1] at h
  rw [h2] at h

  have h_eq1 : a ^ 2 + a - 2 = 0 := h.1
  have h_eq2 : (a - 1) * (a + 2) = 0 := by nlinarith

  cases' (mul_eq_zero.mp h_eq2) with h_a1 h_a2
  · -- a = 1, check the second part of h: a ^ 2 - 3 * a + 2 ≠ 0
    have h_a1' : a = 1 := by linarith
    rw [h_a1'] at h
    norm_num at h
    <;> tauto
  · -- a = -2
    linarith