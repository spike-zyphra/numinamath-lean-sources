import Mathlib

/-Given the function $f(x)=ax^{3}+x^{2}$ $(a\in\mathbb{R})$, the function takes an extreme value at $x=-\frac{4}{3}$. Find the value of $a$.-/
theorem algebra_9430 {a : ℝ} (f : ℝ → ℝ) (hf : f = fun x => a * x ^ 3 + x ^ 2)
  (h' : IsLocalExtr f (-4 / 3) ) : a = 1 / 2 := by
    -- Since the function $f(x)$ takes an extreme value at $x=-\frac{4}{3}$, $f'(-\frac{4}{3})= 0$
    replace h' := IsLocalExtr.deriv_eq_zero h'
    -- f'(x) 3 * a * x^2 + 2 * x.
    have hfderiv : deriv f = fun x => 3 * a * x^2 + 2 * x := by
      ext x
      rw [hf, deriv_add, deriv_pow, deriv_const_mul, deriv_pow]
      simp
      ring
      exact differentiableAt_pow 3
      exact DifferentiableAt.const_mul (differentiableAt_pow 3) a
      exact differentiableAt_pow 2
    -- Calculate the derivative of the function at -4/3, we get a = 1 / 2.
    simp [hfderiv] at h'
    ring_nf at h'
    linarith
