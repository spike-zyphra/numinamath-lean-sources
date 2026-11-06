import Mathlib

open Real Set
open scoped Real

/- 4. Prove: (1) $\sin \alpha+\sin \beta+\sin \gamma-\sin (\alpha+\beta+\gamma)$

$$

=4 \sin \frac{\alpha+\beta}{2} \sin \frac{\beta+\gamma}{2} \sin \frac{\gamma+\alpha}{2} \text {; }

$$

(2)

$$

\begin{array}{c}
\cos \alpha+\cos \beta+\cos \gamma+\cos (\alpha+\beta+\gamma) \\
=4 \cos \frac{\alpha+\beta}{2} \cos \frac{\beta+\gamma}{2} \cos \frac{\gamma+\alpha}{2} .
\end{array}

$$
 -/
theorem algebra_181840 (α β γ : ℝ) :
  sin α + sin β + sin γ - sin (α + β + γ) =
  4 * sin ((α + β) / 2) * sin ((β + γ) / 2) * sin ((γ + α) / 2) ∧
  cos α + cos β + cos γ + cos (α + β + γ) =
  4 * cos ((α + β) / 2) * cos ((β + γ) / 2) * cos ((γ + α) / 2) := by
  constructor
  · suffices sin α + sin β + sin γ - sin (α + β + γ) = 2 * (2 * sin ((α + β) / 2) * sin ((β + γ) / 2)) * sin ((γ + α) / 2) by linarith
    -- Use product to sum on sin*sin, then use product to sum twice on sin*cos
    rw [two_mul_sin_mul_sin, mul_assoc, sub_mul, mul_sub, mul_comm (cos _), mul_comm (cos _), ← mul_assoc, ← mul_assoc, two_mul_sin_mul_cos, two_mul_sin_mul_cos]
    -- Simplify
    ring
    rw [sin_neg]
    ring
  suffices cos α + cos β + cos γ + cos (α + β + γ) = 2 * (2 * cos ((α + β) / 2) * cos ((β + γ) / 2)) * cos ((γ + α) / 2) by linarith
  -- Use product to sum on cos*cos three times
  rw [two_mul_cos_mul_cos, mul_assoc, add_mul, mul_add, ← mul_assoc, ← mul_assoc, two_mul_cos_mul_cos, two_mul_cos_mul_cos]
  -- Simplify
  ring
  rw [cos_neg]
  linarith