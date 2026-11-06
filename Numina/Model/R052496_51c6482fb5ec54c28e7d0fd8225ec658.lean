import Mathlib

theorem algebra_13840 {a b c d : ℝ} (f : ℂ → ℂ) (hf : ∀ x, f x = x ^ 4 + a * x ^ 3 + b * x ^ 2 + c * x + d)
    (h2i : f (2 * Complex.I) = 0) (h2i' : f (2 + Complex.I) = 0) : a + b + c + d = 9 := by
  simp [hf, pow_two, pow_three, pow_succ, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at h2i h2i'
  ring_nf at h2i h2i'
  norm_num at h2i h2i'
  linarith