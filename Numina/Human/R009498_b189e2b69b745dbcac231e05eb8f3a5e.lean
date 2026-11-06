import Mathlib


/-
Given that $m$ is a root of the equation $x^{2}-2x-3=0$, find the value of $2m^{2}-4m$.
-/

theorem algebra_9115 {m : ℝ} (hm : m ^ 2 - 2 * m - 3 = 0) : 2 * m ^ 2 - 4 * m = 6 := by
  -- We add $3$ to both sides of the equation: $$m^{2}-2m = 3$$
  have : m ^ 2 - 2 * m = 3 := by
    rw [← sub_add_cancel 3 3, sub_self, ← hm, sub_add_cancel]

  -- Next, we multiply the entire equation by $2$ to align with the expression $2m^{2}-4m$:
  -- $$2(m^{2}-2m) = 2 \times 3$$
  -- $$2m^{2}-4m = 6$$
  rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_assoc, ← mul_sub 2, this]
  norm_num
