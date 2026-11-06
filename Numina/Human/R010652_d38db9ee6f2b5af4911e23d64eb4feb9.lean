import Mathlib


/-
Given that $f(x)$ is an odd function on $\mathbb{R}$, and when $x > 0$, $f(x)=\sqrt{x}$, find $f(-9)$ ___.
-/

theorem algebra_9187
    {f : ℝ → ℝ}
    (hodd : ∀ x, f (-x) = - f (x))
    (hfpos : ∀ x > 0, f x = Real.sqrt x) :
    f (-9) = -3 := by

  -- $f(9) = \sqrt{9} = 3$.
  have r1 : f 9 = 3 := by
    rw [hfpos 9 (by linarith), show (9:ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

  -- Using the odd function property, $f(-9) = -f(9) = -3$.
  rw [hodd, r1]
