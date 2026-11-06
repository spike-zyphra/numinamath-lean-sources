import Mathlib

open Real Set
open scoped Real

/-Given the function $f(x) = \sin(x + 2\varphi) - 2\sin\varphi\cos(x + \varphi)$, then $f\left( \frac{\pi}{4} \right) = \_\_\_\_\_\_$.-/
theorem algebra_9373 {φ : ℝ} (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = sin (x + 2 * φ) - 2 * sin φ * cos (x + φ)) :
  f (π / 4) = sqrt 2 / 2 := by
    -- Since $f(x) = \sin(x + 2\varphi) - 2\sin\varphi\cos(x + \varphi) = \sin(x + \varphi)\cos\varphi + \cos(x + \varphi)\sin\varphi - 2\sin\varphi\cos(x + \varphi)$
    -- $= \sin(x + \varphi)\cos\varphi - \cos(x + \varphi)\sin\varphi = \sin x$,
    simp [h₀, sin_add, cos_add, cos_two_mul, sin_two_mul]
    ring_nf
    -- then $f\left( \frac{\pi}{4} \right) = \sin \frac{\pi}{4} = \frac{\sqrt{2}}{2}$,
    rw [add_assoc, ←mul_add, Real.cos_sq_add_sin_sq]
    ring
