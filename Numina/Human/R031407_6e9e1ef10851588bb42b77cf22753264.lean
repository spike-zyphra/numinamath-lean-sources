import Mathlib
/- Example 5 (W $\mathrm{W}$ Janous Conjecture) Let $x, y, z \in \mathbf{R}^{+}$. Prove that: $\frac{y^{2}-x^{2}}{z+x}+\frac{z^{2}-y^{2}}{x+y}+\frac{x^{2}-z^{2}}{y+z} \geqslant 0$. -/
theorem inequalities_323830 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    0 ≤ (y ^ 2 - x ^ 2) / (z + x) + (z ^ 2 - y ^ 2) / (x + y) + (x ^ 2 - z ^ 2) / (y + z) := by
  -- First, we prove that the product of the denominators is positive
  have h4 : 0 < (z + x) * (x + y) * (y + z) := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  -- We rewrite the expression to show it equals a non-negative value divided by a positive value
  have h : (y ^ 2 - x ^ 2) / (z + x) + (z ^ 2 - y ^ 2) / (x + y) + (x ^ 2 - z ^ 2) / (y + z) =
        (1 / 2) * ((x^2 - y^2) ^ 2 + (y^2 - z^2) ^ 2 + (z^2 - x^2) ^ 2) / ((z + x) * (x + y) * (y + z)) := by
    -- Prove that all denominators are non-zero
    have h1 : (z + x) ≠ 0 := by nlinarith
    have h2 : (x + y) ≠ 0 := by nlinarith
    have h3 : (y + z) ≠ 0 := by nlinarith
    -- Simplify the expression using field operations and ring normalization
    field_simp [h1, h2, h3]
    ring_nf
  -- Apply the rewritten form of the expression
  rw [h]
  -- Prove the inequality by showing a non-negative value divided by a positive value is non-negative
  apply div_nonneg
  -- The numerator is non-negative as it's a sum of squared terms
  ·
    nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (y^2 - z^2), sq_nonneg (z^2 - x^2)]
  -- The denominator is positive as already proven in h4
  ·
    all_goals nlinarith [h4]
