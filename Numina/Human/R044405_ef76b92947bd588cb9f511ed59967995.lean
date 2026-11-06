import Mathlib


/- Simplify $\sqrt{15}\cdot\sqrt{35}$. -/
theorem algebra_21033 :
    Real.sqrt 15 * Real.sqrt 35 = 5 * Real.sqrt 21 := by

  -- Place under one square root and simplify:
  calc
    -- \sqrt{15}\cdot\sqrt{35} &= \sqrt{15\cdot35}
    _ = Real.sqrt (15 * 35) := by
      rw [← Real.sqrt_mul (by linarith only)]
    -- =\sqrt{3\cdot5^2\cdot7}
    _ = Real.sqrt (3 * 5 ^ 2 * 7) := by
      ring_nf
    -- =\sqrt{5^2}\cdot\sqrt{3\cdot7}
    _ = Real.sqrt (5 ^ 2) * Real.sqrt (3 * 7) := by
      rw [mul_comm 3, mul_assoc, Real.sqrt_mul (by linarith only)]
    -- = \boxed{5\sqrt{21}}
    _ = 5 * Real.sqrt 21 := by
      rw [Real.sqrt_sq (by linarith only)]
      norm_num
