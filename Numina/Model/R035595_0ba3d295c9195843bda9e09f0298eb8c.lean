import Mathlib

theorem algebra_256719 (k : ℝ) (hk : k < 0) :
    ∀ z : ℂ, 10 * z ^ 2 - 3 * Complex.I * z - k = 0 →
      ∃ w : ℂ, w ≠ z ∧ 10 * w ^ 2 - 3 * Complex.I * w - k = 0 ∧
        (z.re = 0 ∧ w.re = 0) := by
  intro z h
  have eq1 : 10 * z ^ 2 - 3 * Complex.I * z - k = 0 := h
  have eq2 := congr_arg Complex.re eq1
  have eq3 := congr_arg Complex.im eq1
  simp [pow_two, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at eq2 eq3
  have h2 : z.re * (20 * z.im - 3) = 0 := by
    nlinarith
  have h3 : z.re = 0 ∨ 20 * z.im - 3 = 0 := by
    cases (mul_eq_zero.1 h2) with
    | inl h5 => 
      left
      linarith
    | inr h6 => 
      right
      linarith
  have h5 : z.re = 0 := by
    rcases h3 with (h5 | h6)
    · 
      tauto
    · 
      -- Assume $20 * z.im - 3 = 0$, derive the contradiction
      have h7 : z.re ^ 2 ≥ 0 := by nlinarith
      nlinarith
  use (3 * Complex.I / 10 - z)
  constructor
  · -- Show that w ≠ z
    by_contra h3
    have h4 : (3 * Complex.I / 10 - z) = z := by
      exact h3
    have h5 : z.re = 0 := h5
    have h6 : z.im = 3 / 20 := by
      have h7 : z.re = 0 := h5
      simp [Complex.ext_iff, h7] at h4
      nlinarith
    -- Substitute z.im = 3/20 into the equation
    rw [show z.re = 0 by linarith] at eq2
    rw [show z.im = 3 / 20 by linarith] at eq2
    nlinarith
  constructor
  · -- Show that 10 w^2 - 3i w - k = 0
    have h12 : 10 * (3 * Complex.I / 10 - z) ^ 2 - 3 * Complex.I * (3 * Complex.I / 10 - z) - k = 0 := by
      have h11 : 10 * z ^ 2 - 3 * Complex.I * z - k = 0 := h
      simp [pow_two, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at h11 ⊢
      ring_nf at h11 ⊢
      constructor
      · -- Real part
        nlinarith
      · -- Imaginary part
        nlinarith
    exact h12
  · -- Show that both roots have real part 0
    constructor
    · -- z.re = 0
      exact h5
    · -- w.re = 0
      simp [Complex.ext_iff, h5, Complex.add_re, Complex.ofReal_re, Complex.I_re, Complex.sub_re]