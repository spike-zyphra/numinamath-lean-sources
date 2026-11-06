import Mathlib


theorem algebra_174973 (a b c d : ℝ) (h : a * b + b * c + c * d + d * a = 1) :
    a^2 + 2 * b^2 + 3 * c^2 + 4 * d^2 ≥ 2 := by
  have h1 : (a + c) * (b + d) = 1 := by
    nlinarith

  have h2 : a ^ 2 + 3 * c ^ 2 ≥ 3 / 4 * (a + c) ^ 2 := by
    nlinarith [sq_nonneg (a - 3 * c)]

  have h3 : 2 * b ^ 2 + 4 * d ^ 2 ≥ 4 / 3 * (b + d) ^ 2 := by
    nlinarith [sq_nonneg (b - 2 * d), sq_nonneg (2 * b - d), sq_nonneg (b + 2 * d)]

  have h4 : a ^ 2 + 2 * b ^ 2 + 3 * c ^ 2 + 4 * d^2 ≥ 3 / 4 * (a + c) ^ 2 + 4 / 3 * (b + d) ^ 2 := by
    nlinarith [h2, h3]

  have h5 : 3 / 4 * (a + c) ^ 2 + 4 / 3 * (b + d) ^ 2 ≥ 2 := by
    have h6 : (a + c) * (b + d) = 1 := h1
    nlinarith [sq_nonneg ((a + c) ^ 2 - 4 / 3), sq_nonneg ((b + d) ^ 2 - 3 / 4), sq_nonneg ((a + c) - 2 / Real.sqrt 3), sq_nonneg ((b + d) - Real.sqrt 3 / 2), sq_nonneg ((a + c) * (b + d) - 1), sq_nonneg ((a + c) ^ 2 - 4 / 3), sq_nonneg ((b + d) ^ 2 - 3 / 4)]

  linarith [h4, h5]