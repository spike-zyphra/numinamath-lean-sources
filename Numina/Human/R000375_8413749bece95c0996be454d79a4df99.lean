import Mathlib

open Real Set
open scoped BigOperators

/- Given the function $f(x)=\sin x+\cos x$, find $f'(\frac{π}{4})$.-/
theorem algebra_9271 {f : ℝ → ℝ} (hf : f = λ x => sin x + cos x) :
    deriv f (π/4) = 0 := by
--   Given the function $f(x) = \sin x + \cos x$, to find the derivative at $x = \frac{\pi}{4}$, we first determine the general form of the derivative of $f(x)$.
-- Starting with:
-- $$f(x)=\sin x + \cos x$$
-- The derivative of $\sin x$ with respect to $x$ is $\cos x$, and the derivative of $\cos x$ with respect to $x$ is $-\sin x$. Therefore, taking the derivative of $f(x)$, we have:
-- $$f'(x) = \frac{d}{dx}(\sin x) + \frac{d}{dx}(\cos x) = \cos x - \sin x$$
-- To find $f'\left(\frac{\pi}{4}\right)$, we substitute $x = \frac{\pi}{4}$ into the derivative:
-- \begin{align*}
-- f'\left(\frac{\pi}{4}\right) &= \cos\left(\frac{\pi}{4}\right) - \sin\left(\frac{\pi}{4}\right) \\
-- &= \frac{\sqrt{2}}{2} - \frac{\sqrt{2}}{2} \\
-- &= 0
-- \end{align*}
-- Therefore, the derivative of $f(x)$ at $x = \frac{\pi}{4}$ is $\boxed{0}$.
  rw [hf, deriv_add, Real.deriv_sin, Real.cos_pi_div_four, Real.deriv_cos, Real.sin_pi_div_four]
  norm_num
  . exact differentiableAt_sin
  . exact differentiableAt_cos
