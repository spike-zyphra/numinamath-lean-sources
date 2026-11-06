import Mathlib

open Real

/- Task 17/80 Prove the validity of the inequality for all real numbers $x$:
$$
\left(x+\frac{1}{2} \sin (2 x)\right)\left(x-\frac{1}{2} \sin (2 x)\right) \geq \sin ^{4} x
$$
 -/
theorem inequalities_158407 (x : ℝ) :
    (x + (1/2)*sin (2*x))*(x - (1/2)*sin (2*x)) ≥ sin x ^ 4 := calc
  (x + (1/2)*sin (2*x))*(x - (1/2)*sin (2*x)) = (x ^ 2 - sin x ^ 2) + sin x ^ 4 := by
      -- We have sin(2x) = 2 sin(x)cos(x).
      rw [sin_two_mul]
      -- After simplifications, we get x^2 - sin(x)^2 cos(x)^2.
      ring_nf
      -- We have cos(x)^2 = 1 - sin(x)^2 and the result follows.
      rw [cos_sq']
      ring
  _ ≥ 0 + sin x ^ 4 := by
      gcongr
      rw [sub_nonneg]
      -- It is left to show that sin(x)^2 ≤ x^2.
      -- This inequality is equivalent to |sin(x)| ≤ |x|.
      rw [sq_le_sq]
      -- |sin(x)| ≤ |x| for all x.
      exact abs_sin_le_abs
  _ = sin x ^ 4 := by rw [zero_add]