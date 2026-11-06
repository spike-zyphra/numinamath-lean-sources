import Mathlib

open Real

/- If $a$, $b$ are nonzero real numbers such that $a^2+b^2=8ab$, find the value of $\left|\frac{a+b}{a-b}\right|$. -/
theorem algebra_11185
    {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a^2 + b^2 = 8 * a * b) :
    |((a + b) / (a - b))| = √ 15 / 3 := by

  calc
    -- = \sqrt{\frac{(a+b)^2}{(a-b)^2}}
    _ = √ ((a + b) ^ 2 / (a - b) ^ 2) := by
      rw [← div_pow, ← sq_abs, sqrt_sq]
      apply abs_nonneg
    -- = \sqrt{\frac{a^2+b^2+2ab}{a^2+b^2-2ab}}
    _ = √ ((a ^ 2 + b ^ 2 + 2 * a * b) / (a ^ 2 + b ^ 2 - 2 * a * b)) := by
      ring_nf
    -- = \sqrt{\frac{10ab}{6ab}}
    _ = √ ((10 * a * b) / (6 * a * b)) := by
      rw [h]
      ring_nf
    -- = \boxed{\frac{\sqrt{15}}{3}}.
    _ = √ 15 / 3 := by
      rw [mul_assoc, mul_assoc, mul_div_mul_right]
      field_simp
      rw [show (3 : ℝ) = √ (3 * 3) by simp, ← sqrt_mul ?_, ← sqrt_mul ?_]
      . ring_nf
      . linarith
      . linarith
      . exact mul_ne_zero ha hb
