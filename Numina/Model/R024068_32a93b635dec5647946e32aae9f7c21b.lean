import Mathlib

open Real

theorem inequalities_29573 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    1 ≤ ((x + y) * (x ^ 3 + y ^ 3)) / (x ^ 2 + y ^ 2) ^ 2 ∧
    ((x + y) * (x ^ 3 + y ^ 3)) / (x ^ 2 + y ^ 2) ^ 2 ≤ 9 / 8 := by
  constructor
  · -- Prove that $1 \leq \frac{(x + y)(x^3 + y^3)}{(x^2 + y^2)^2}$.
    have h1 : 0 < x ^ 2 + y ^ 2 := by
      nlinarith [show 0 < x by linarith, show 0 < y by linarith]
    have h2 : ((x + y) * (x ^ 3 + y ^ 3)) ≥ (x ^ 2 + y ^ 2) ^ 2 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy, mul_self_nonneg (x * y)]
    have h3 : ((x + y) * (x ^ 3 + y ^ 3)) / (x ^ 2 + y ^ 2) ^ 2 ≥ (1 : ℝ) := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith [show ((x + y) * (x ^ 3 + y ^ 3)) ≥ (x ^ 2 + y ^ 2) ^ 2 by nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy]]
    exact h3
  · -- Prove that $\frac{(x + y)(x^3 + y^3)}{(x^2 + y^2)^2} \leq \frac98$.
    have h1 : 0 < x ^ 2 + y ^ 2 := by
      nlinarith [show 0 < x by linarith, show 0 < y by linarith]
    have h4 : ((x + y) * (x ^ 3 + y ^ 3)) / (x ^ 2 + y ^ 2) ^ 2 ≤ (9 / 8 : ℝ) := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith [sq_nonneg (x ^ 2 - 4 * x * y + y ^ 2), sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy, mul_self_nonneg (x * y), sq_nonneg (x^2 - y^2)]
    exact h4