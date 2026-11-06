import Mathlib

theorem algebra_224858 (a b c d : ℝ) (h : a^6 + b^6 + c^6 + d^6 = 64) :
    a^7 + b^7 + c^7 + d^7 ≤ 128 := by

  have h1 : a^6 ≥ 0 := by positivity
  have h2 : b^6 ≥ 0 := by positivity
  have h3 : c^6 ≥ 0 := by positivity
  have h4 : d^6 ≥ 0 := by positivity

  have h5 : a^6 ≤ 64 := by
    nlinarith [sq_nonneg (b^3), sq_nonneg (c^3), sq_nonneg (d^3), sq_nonneg (b^2), sq_nonneg (c^2), sq_nonneg (d^2)]

  have h6 : b^6 ≤ 64 := by
    nlinarith [sq_nonneg (a^3), sq_nonneg (c^3), sq_nonneg (d^3), sq_nonneg (a^2), sq_nonneg (c^2), sq_nonneg (d^2)]

  have h7 : c^6 ≤ 64 := by
    nlinarith [sq_nonneg (a^3), sq_nonneg (b^3), sq_nonneg (d^3), sq_nonneg (a^2), sq_nonneg (b^2), sq_nonneg (d^2)]

  have h8 : d^6 ≤ 64 := by
    nlinarith [sq_nonneg (a^3), sq_nonneg (b^3), sq_nonneg (c^3), sq_nonneg (a^2), sq_nonneg (b^2), sq_nonneg (c^2)]

  have h10 : a ≤ 2 := by
    nlinarith [sq_nonneg (a^3 - 8), sq_nonneg (a^2 - 4), sq_nonneg (a - 2), sq_nonneg (a^3), sq_nonneg (a^2 - 4)]

  have h11 : b ≤ 2 := by
    nlinarith [sq_nonneg (b^3 - 8), sq_nonneg (b^2 - 4), sq_nonneg (b - 2), sq_nonneg (b^3), sq_nonneg (b^2 - 4)]

  have h12 : c ≤ 2 := by
    nlinarith [sq_nonneg (c^3 - 8), sq_nonneg (c^2 - 4), sq_nonneg (c - 2), sq_nonneg (c^3), sq_nonneg (c^2 - 4)]

  have h13 : d ≤ 2 := by
    nlinarith [sq_nonneg (d^3 - 8), sq_nonneg (d^2 - 4), sq_nonneg (d - 2), sq_nonneg (d^3), sq_nonneg (d^2 - 4)]

  have h14 : a^7 ≤ 2 * a^6 := by
    nlinarith [sq_nonneg (a^3), sq_nonneg (a - 2), sq_nonneg (a^2 - 2), h10, sq_nonneg (a^3 - 8), sq_nonneg (a^2 - 4)]

  have h15 : b^7 ≤ 2 * b^6 := by
    nlinarith [sq_nonneg (b^3), sq_nonneg (b - 2), sq_nonneg (b^2 - 2), h11, sq_nonneg (b^3 - 8), sq_nonneg (b^2 - 4)]

  have h16 : c^7 ≤ 2 * c^6 := by
    nlinarith [sq_nonneg (c^3), sq_nonneg (c - 2), sq_nonneg (c^2 - 2), h12, sq_nonneg (c^3 - 8), sq_nonneg (c^2 - 4)]

  have h17 : d^7 ≤ 2 * d^6 := by
    nlinarith [sq_nonneg (d^3), sq_nonneg (d - 2), sq_nonneg (d^2 - 2), h13, sq_nonneg (d^3 - 8), sq_nonneg (d^2 - 4)]

  have h18 : a^7 + b^7 + c^7 + d^7 ≤ 2 * (a^6 + b^6 + c^6 + d^6) := by
    linarith [h14, h15, h16, h17]

  nlinarith [h18, h]