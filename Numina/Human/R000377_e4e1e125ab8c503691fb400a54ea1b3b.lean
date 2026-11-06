import Mathlib

/-Given that $f(x)$ is a function whose derivative is $f'(x)$, and it satisfies the equation $f(x) = 2x^2 - xf'(2)$, find $f'(5)$.-/
theorem algebra_9289 {f : ℝ → ℝ}
  (h : ∀ x, f x = 2 * x ^ 2 - x * deriv f 2) : deriv f 5 = 16 := by
    -- differentiate both sides of the equation: $$f'(x) = \frac{d}{dx}(2x^2) - \frac{d}{dx}(xf'(2))$$
    -- Solving this we get: $$f'(x) = 4x - f'(2)$$
    have h1 (x : ℝ) : deriv f x = 4 * x - deriv f 2 := by
      nth_rewrite 1 [funext h]
      rw [deriv_sub, deriv_const_mul,deriv_pow 2, deriv_mul_const]
      simp
      ring
      · exact differentiableAt_id'
      · exact differentiableAt_pow 2
      · apply DifferentiableAt.const_mul
        exact differentiableAt_pow 2
      · apply DifferentiableAt.mul_const
        exact differentiableAt_id'
    -- Let's plug in $x = 2$ to find the value of $f'(2)$, then we get `deriv f 2 = 4`
    have :=  h1 2
    have h2 : deriv f 2 = 4 := by linarith
    simp [h2] at h1
    -- Substitute $x = 5$ to find $f'(5)$:
    -- Then we get the value of $f'(5)$ is $\boxed{16}$.
    specialize h1 5
    simp [h1]
    ring
