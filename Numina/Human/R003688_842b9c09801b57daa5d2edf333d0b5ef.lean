import Mathlib

/- 1. If $x-y=12$, find the value of $x^{3}-y^{3}-36 x y$.
(1 mark)
If $x-y=12$, find the value of $x^{3}-y^{3}-36 x y$.
(1 mark) -/
theorem algebra_207486 {x y : ℝ}
    (h : x - y = 12) : x ^ 3 - y ^ 3 - 36 * x * y = 1728 := by

  have l_1 (a b : ℝ) : a ^ 3 - b ^ 3 = (a - b) * (a ^ 2 + a * b + b ^ 2) := by
    ring

  have r1 : x ^ 3 - y ^ 3 = (x - y) * (x ^ 2 + x * y + y ^ 2) := by
    exact l_1 x y

  calc
    _ = 12 * (x ^ 2 + x * y + y ^ 2) - 36 * x * y := by
      rw [r1, h]
    _ = 12 * (x ^ 2 - 2 * x * y + y ^ 2) := by
      ring
    _ = 12 * (x - y) ^ 2 := by
      rw [← sub_sq]
    _ = 1728 := by
      rw [h]
      norm_num