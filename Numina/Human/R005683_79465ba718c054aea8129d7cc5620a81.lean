import Mathlib
open Real

/-
Evaluate

$$
\sin (\arcsin (0.4)+\arcsin (0.5)) \cdot \sin (\arcsin (0.5)-\arcsin (0.4))
$$

where for $x \in[-1,1], \arcsin (x)$ denotes the unique real number $y \in[-\pi, \pi]$ such that $\sin (y)=x$.
-/
theorem algebra_609390 : sin (arcsin 0.4 + arcsin 0.5)* sin (arcsin 0.5 - arcsin 0.4) = 0.09 := by

  -- We will use the following facts:
  -- sin(arcsin x) = x
  have hsin4: sin (arcsin 0.4) = 0.4 := by
    exact sin_arcsin (by norm_num) (by norm_num)
  have hsin5: sin (arcsin 0.5) = 0.5 := by
    exact sin_arcsin (by norm_num) (by norm_num)

  rw [show sin (arcsin 0.4 + arcsin 0.5)* sin (arcsin 0.5 - arcsin 0.4) = sin (arcsin 0.5 + arcsin 0.4)* sin (arcsin 0.5 - arcsin 0.4) by ring_nf]

  -- We will use the following facts:
  -- sin(x + y) = sin(x)cos(y) + cos(x)sin(y)
  -- sin(x - y) = sin(x)cos(y) - cos(x)sin(y)
  -- sin(x)^2 + cos(x)^2 = 1
  -- cos^2(arcsin x) = 1 - x^2
  rw [sin_sub (arcsin 0.5) (arcsin 0.4), sin_add (arcsin 0.5) (arcsin 0.4)]
  calc
    _ = (sin (arcsin 0.5))^2 * (cos (arcsin 0.4))^2 - (cos (arcsin 0.5))^2 * (sin (arcsin 0.4))^2 := by ring_nf
    _ = 0.5^2 * (cos (arcsin 0.4))^2 - (cos (arcsin 0.5))^2 * 0.4^2 := by rw [hsin5, hsin4]
    _ = 0.5^2 * (1 - sin (arcsin 0.4)^2) - (1 - sin (arcsin 0.5)^2) * 0.4^2 := by
      have _1: 1 = sin (arcsin 0.4)^2 + cos (arcsin 0.4)^2 := by rw [←sin_sq_add_cos_sq (arcsin 0.4)]
      have _2: 1 = sin (arcsin 0.5)^2 + cos (arcsin 0.5)^2 := by rw [←sin_sq_add_cos_sq (arcsin 0.5)]
      have _1': cos (arcsin 0.4)^2 = 1 - sin (arcsin 0.4)^2 := by linarith
      have _2': cos (arcsin 0.5)^2 = 1 - sin (arcsin 0.5)^2 := by linarith
      rw [_1', _2']
    _ = 0.5^2 * (1 - 0.4^2) - (1 - 0.5^2) * 0.4^2 := by rw [hsin5, hsin4]
    _ = 0.09 := by
      ring_nf
