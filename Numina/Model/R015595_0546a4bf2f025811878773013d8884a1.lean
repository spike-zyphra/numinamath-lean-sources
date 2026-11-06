import Mathlib

theorem inequalities_7218 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hsum : x + y + z = 2) :
    x / (y ^ 2 + 1) + y / (z ^ 2 + 1) + z / (x ^ 2 + 1) ≤ 2 := by

  have h1 : x / (y^2 + 1) ≤ x := by
    have h2 : y^2 + 1 ≥ 1 := by
      nlinarith [sq_nonneg y]
    apply (div_le_iff₀ (by nlinarith)).mpr
    nlinarith [sq_nonneg y, mul_nonneg hx (show 0 ≤ y ^ 2 by positivity)]

  have h2 : y / (z^2 + 1) ≤ y := by
    have h3 : z^2 + 1 ≥ 1 := by
      nlinarith [sq_nonneg z]
    apply (div_le_iff₀ (by nlinarith)).mpr
    nlinarith [sq_nonneg z, mul_nonneg (show 0 ≤ y by linarith) (show 0 ≤ z ^ 2 by positivity)]

  have h3 : z / (x^2 + 1) ≤ z := by
    have h4 : x^2 + 1 ≥ 1 := by
      nlinarith [sq_nonneg x]
    apply (div_le_iff₀ (by nlinarith)).mpr
    nlinarith [sq_nonneg x, mul_nonneg (show 0 ≤ z by linarith) (show 0 ≤ x ^ 2 by positivity)]

  have h4 : x + y + z = 2 := hsum

  have h5 : x / (y^2 + 1) + y / (z^2 + 1) + z / (x^2 + 1) ≤ x + y + z := by
    linarith [h1, h2, h3]

  have h6 : x + y + z = 2 := hsum

  linarith [h5, h6]