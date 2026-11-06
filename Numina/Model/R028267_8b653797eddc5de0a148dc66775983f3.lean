import Mathlib

theorem inequalities_224323 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    1 ≤ ((x + y) * (x ^ 3 + y ^ 3)) / (x ^ 2 + y ^ 2) ^ 2 ∧
    ((x + y) * (x ^ 3 + y ^ 3)) / (x ^ 2 + y ^ 2) ^ 2 ≤ 9 / 8 := by

  have h1 : 0 < x ^ 2 + y ^ 2 := by
    nlinarith

  constructor

  · -- Prove 1 ≤ ((x + y) * (x ^ 3 + y ^ 3)) / (x ^ 2 + y ^ 2) ^ 2
    have h2 : ((x + y) * (x ^ 3 + y ^ 3)) ≥ (x ^ 2 + y ^ 2) ^ 2 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy, mul_pos hx (show 0 < x ^ 2 by positivity), mul_pos hy (show 0 < y ^ 2 by positivity)]
    have h3 : ((x + y) * (x ^ 3 + y ^ 3)) / (x ^ 2 + y ^ 2) ^ 2 ≥ 1 := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith
    exact h3

  · -- Prove ((x + y) * (x ^ 3 + y ^ 3)) / (x ^ 2 + y ^ 2) ^ 2 ≤ 9 / 8
    have h4 : ((x + y) * (x ^ 3 + y ^ 3)) ≤ (9 / 8) * (x ^ 2 + y ^ 2) ^ 2 := by
      nlinarith [sq_nonneg (x ^ 2 - 4 * x * y + y ^ 2), sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy, mul_pos hx (show 0 < x ^ 2 by positivity), mul_pos hy (show 0 < y ^ 2 by positivity)]
    have h5 : ((x + y) * (x ^ 3 + y ^ 3)) / (x ^ 2 + y ^ 2) ^ 2 ≤ 9 / 8 := by
      apply (div_le_iff₀ (by positivity)).mpr
      linarith
    exact h5