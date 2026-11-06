import Mathlib

open Real Set

/- 2. If the real numbers $x, y, z \in [0, +\infty)$ satisfy the relations:

$$
\frac{x+y}{2} \leq \sqrt{x \cdot y} + 1 \text{ and } \frac{y+z}{2} \leq \sqrt{y \cdot z} + 4
$$

prove that $|\sqrt{z} - \sqrt{x}| \leq 3 \sqrt{2}$.

Marius Damian, Brăila -/
theorem inequalities_115477 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h1 : (x + y) / 2 ≤ sqrt (x * y) + 1) (h2 : (y + z) / 2 ≤ sqrt (y * z) + 4) :
    |sqrt z - sqrt x| ≤ 3 * sqrt 2 := by

    -- we first show that:
    -- (x + y) / 2 ≤ √ (x * y) + 1 →
    -- x - 2 * √ (x * y) + y ≤ 2 →
    -- (√ x - √ y) ^ 2 ≤ 2 →
    -- |√ x - √ y| ≤ √ 2
    have : x - 2 * √ (x * y) + y ≤ 2 := by linarith
    have : (√ x - √ y) ^ 2 ≤ 2 := by
      rw [sub_pow_two, sq_sqrt hx, sq_sqrt hy, mul_assoc, ← sqrt_mul hx]
      exact this
    rw [(by norm_num : 2 = √ 2 ^ 2)] at this
    have hxy := abs_le_of_sq_le_sq this (by norm_num)

    -- we then show that:
    -- (y + z) / 2 ≤ √ (x * y) + 4 →
    -- y - 2 * √ (y * z) + z ≤ 8 ≤ 2 →
    -- (√ y - √ z) ^ 2 ≤ 8 →
    -- |√ y - √ z| ≤ 2 * √ 2
    have : y - 2 * √ (y * z) + z ≤ 8 := by linarith
    have : (√ y - √ z) ^ 2 ≤ 8 := by
      rw [sub_pow_two, sq_sqrt hy, sq_sqrt hz, mul_assoc, ← sqrt_mul hy]
      exact this
    rw [(by rw [mul_pow]; norm_num : 8 = (2 * √ 2) ^ 2)] at this
    have hyz := abs_le_of_sq_le_sq this (by norm_num)

    -- finally we prove the theorem by triangle inequality
    calc
      |sqrt z - sqrt x| = |(sqrt z - sqrt y) + (sqrt y - sqrt x)| := by simp
      _ ≤ |sqrt z - sqrt y| + |sqrt y - sqrt x| := by apply abs_add_le
      _ = |sqrt y - sqrt z| + |sqrt x - sqrt y| := by simp [abs_sub_comm]
      _ ≤ 2 * √ 2 + √ 2 := by linarith [hyz, hxy]
      _ = 3 * √ 2 := by linarith
