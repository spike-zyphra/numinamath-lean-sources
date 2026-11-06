import Mathlib

/-
11. (16 points) Given positive real numbers $x, y, z$ satisfy
$$
9xyz + xy + yz + zx = 4 \text{.}
$$

Prove: (1) $xy + yz + zx \geqslant \frac{4}{3}$;
$$
\text{(2) } x + y + z \geqslant 2 \text{.}
$$
-/
theorem inequalities_306868 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : 9 * x * y * z + x * y + y * z + z * x = 4) :
    x * y + y * z + z * x ≥ 4 / 3 ∧ x + y + z ≥ 2 := by
  have h1 : x * y + y * z + z * x ≥ 4 / 3 := by
    nlinarith [sq_nonneg (x - 2 / 3), sq_nonneg (y - 2 / 3), sq_nonneg (z - 2 / 3),
      sq_nonneg (x * y - 4 / 9), sq_nonneg (y * z - 4 / 9), sq_nonneg (z * x - 4 / 9),
      mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, h]
  have h2 : x + y + z ≥ 2 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      h1, mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, h]
  exact ⟨h1, h2⟩