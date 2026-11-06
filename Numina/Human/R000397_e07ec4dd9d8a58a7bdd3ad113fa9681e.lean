import Mathlib


/-
Given a function $f(x) = x\sin 2x$, find $f'(\frac{\pi}{2})$.
-/

theorem algebra_9451
    {f : ℝ → ℝ}
    (hf : f = fun x => x * Real.sin (2 * x)) :
    deriv f (Real.pi / 2) = - Real.pi := by

  /-
  To find the derivative of the function $f(x) = x\sin 2x$, we apply the product rule for differentiation, which states that $(uv)' = u'v + uv'$. Here, $u = x$ and $v = \sin 2x$.

  1. Differentiate $u = x$ with respect to $x$ to get $u' = 1$.
  2. Differentiate $v = \sin 2x$ with respect to $x$ to get $v' = 2\cos 2x$ using the chain rule.
  3. Apply the product rule: $f'(x) = u'v + uv' = 1 \cdot \sin 2x + x \cdot 2\cos 2x = \sin 2x + 2x\cos 2x$.

  Now, to find $f'(\frac{\pi}{2})$:

  1. Substitute $x = \frac{\pi}{2}$ into $f'(x)$: $f'(\frac{\pi}{2}) = \sin (\pi) + 2 \times \frac{\pi}{2} \cos (\pi)$.
  2. Calculate each term: $\sin (\pi) = 0$ and $\cos (\pi) = -1$.
  3. Therefore, $f'(\frac{\pi}{2}) = 0 + 2 \times \frac{\pi}{2} \times (-1) = -\pi$.

  Hence, the derivative of the function $f(x)$ at $x = \frac{\pi}{2}$ is $\boxed{-\pi}$.
  -/

  rw [hf, deriv_mul, deriv_id'', deriv_sin, deriv_mul, deriv_const, deriv_id'']

  simp [mul_div_cancel₀]

  any_goals simp

  . show DifferentiableAt ℝ (HMul.hMul 2) (Real.pi / 2)
    apply DifferentiableAt.const_mul ?_ 2
    exact differentiableAt_id'

  . show DifferentiableAt ℝ (fun x => Real.sin (2 * x)) (Real.pi / 2)
    apply DifferentiableAt.sin ?_
    apply DifferentiableAt.const_mul ?_ 2
    exact differentiableAt_id'
