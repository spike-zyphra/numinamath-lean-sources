import Mathlib

theorem algebra_196878 (lambda : ℝ) :
    (∀ x : ℂ, (1 - Complex.I) * x ^ 2 + (lambda + Complex.I) * x + (1 + Complex.I * lambda) = 0 →
      x.im ≠ 0) ↔ lambda ≠ 2 := by
  constructor
  · -- Assume that all roots are non-real, prove $\lambda \neq 2$
    intro h
    by_contra h1
    -- Assume $\lambda = 2$, prove there is a real root
    have h2 : lambda = 2 := by
      simpa using h1
    -- Check x = -1 is a root when $\lambda = 2$
    have h3 := h (-1 : ℂ) (by
      rw [show lambda = (2 : ℝ) by linarith [h2]]
      simp [pow_two, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      all_goals norm_num
    )
    -- Contradiction: x = -1 is real
    norm_num at h3
  · -- Assume $\lambda \neq 2$, prove all roots are non-real
    intro h1 x hx
    by_contra h2
    -- Assume x is real, prove a contradiction
    have h2' : x.im = 0 := by
      simpa using h2
    -- Extract real and imaginary parts of the equation
    have eq1 := congr_arg Complex.re hx
    have eq2 := congr_arg Complex.im hx
    -- Simplify equations
    simp [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, h2', mul_add, mul_comm] at eq1 eq2
    -- Real part: x.re ^ 2 + lambda * x.re + 1 = 0
    -- Imaginary part: x.re - x.re ^ 2 + lambda = 0
    have h3 : x.re ^ 2 + lambda * x.re + 1 = 0 := by linarith [eq1]
    have h4 : x.re - x.re ^ 2 + lambda = 0 := by linarith [eq2]
    -- Derive contradiction
    have h9 : lambda = 2 := by 
      nlinarith [sq_pos_of_ne_zero (show lambda - 2 ≠ 0 by 
        intro h8
        apply h1
        linarith
      ), sq_nonneg (x.re + 1), sq_nonneg (lambda - 2)]
    -- Contradicts the hypothesis $\lambda \neq 2$
    have h10 : lambda = 2 := h9
    have h11 : lambda ≠ 2 := h1
    contradiction