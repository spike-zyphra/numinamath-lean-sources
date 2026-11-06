import Mathlib

theorem algebra_21997 {b : ℝ} (hb : b > 0) (z : ℂ) (hz : z = 9 + Complex.I * b)
    (h : (z ^ 2).im = (z ^ 3).im) : b = 15 := by
  rw [hz] at h
  simp [pow_two, pow_succ, Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.I_im, Complex.I_re, mul_add, add_mul] at h 
  have h1 : b ^ 3 - 225 * b = 0 := by
    nlinarith
  have h2 : b * (b ^ 2 - 225) = 0 := by
    ring_nf at h1 ⊢
    linarith
  cases' (mul_eq_zero.mp h2) with hb1 hb2
  · -- Case b = 0
    nlinarith
  · -- Case b^2 - 225 = 0
    have h3 : b ^ 2 = 225 := by linarith
    have h4 : b = 15 := by
      nlinarith [sq_pos_of_pos hb]
    linarith