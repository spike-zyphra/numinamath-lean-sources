import Mathlib

theorem algebra_20382 (k : ℝ) (h : ∃ x1 x2 : ℂ, x1 ≠ x2 ∧ 4 * x1 ^ 2 + 7 * x1 + k = 0 ∧ 4 * x2 ^ 2 + 7 * x2 + k = 0 ∧ x1 = -7 / 8 + Real.sqrt 15 / 8 * Complex.I ∧ x2 = -7 / 8 - Real.sqrt 15 / 8 * Complex.I) :
    k = 4 := by

  rcases h with ⟨x1, x2, h12, h1, h2, hx1, hx2⟩

  rw [hx1] at h1
  rw [hx2] at h2

  simp [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, pow_two, Complex.I_re, Complex.I_im, mul_add, mul_comm] at h1 h2
  ring_nf at h1 h2
  norm_num [Real.sqrt_sq] at h1 h2

  linarith