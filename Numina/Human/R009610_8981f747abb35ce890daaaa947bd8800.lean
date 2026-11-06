import Mathlib

open Real Set
open scoped BigOperators

/-Given the function $f(x) = x\sin{x}$, find $f'(\frac{\pi}{4})$.-/
theorem algebra_9331 {f : ℝ → ℝ} (hf : f = λ x => x * sin x) :
    deriv f (Real.pi/4) = Real.sqrt 2 / 2 + Real.sqrt 2 * Real.pi / 8 := by
  -- To solve, we first find the derivative of $f(x)$ using product rule, which is $f'(x) = (x\sin{x})' = \sin{x} + x\cos{x}$.
  have : deriv f = fun x => x * cos x + sin x := by
    ext x; rw [hf, deriv_mul]
    simp only [deriv_id'', one_mul, Real.deriv_sin]; ring_nf
    simp only [differentiableAt_id']
    exact differentiableAt_sin
  -- Therefore, $f'(\frac{\pi}{4}) = \sin{\frac{\pi}{4}} + \frac{\pi}{4}\cos{\frac{\pi}{4}} = \frac{\sqrt{2}}{2} + \frac{\sqrt{2}\pi}{8}$.
  rw [this]; simp only [cos_pi_div_four, sin_pi_div_four]; ring