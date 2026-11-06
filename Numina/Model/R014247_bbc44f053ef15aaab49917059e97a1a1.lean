import Mathlib

open Real


lemma lemma_1 (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    u ^ 2 * v ^ 3 ≤ (2 / 5) * u ^ 5 + (3 / 5) * v ^ 5 := by

  have h1 : 2 * u ^ 5 - 5 * u ^ 2 * v ^ 3 + 3 * v ^ 5 ≥ 0 := by

    nlinarith [sq_nonneg (u ^ 2 - v ^ 2), sq_nonneg (u ^ 2 - u * v), sq_nonneg (v ^ 2 - u * v),
      sq_nonneg (u - v), sq_nonneg (u + v), sq_nonneg (u ^ 2 - v * u), sq_nonneg ((u - v) * (u + v)), sq_nonneg ((u - v) * (u - v)), sq_nonneg ((u) ^ 2 - (v) ^ 2), sq_nonneg (u * v - v ^ 2), sq_nonneg (u * v - u ^ 2), mul_pos hu hv, mul_pos hu (show 0 < v ^ 2 by positivity), mul_pos (show 0 < u ^ 2 by positivity) hv]

  nlinarith


theorem inequalities_602658
    (a b x y : ℝ)
    (ha : 0 ≤ a ∧ a > 0)
    (hb : 0 ≤ b ∧ b > 0)
    (hx : 0 ≤ x ∧ x > 0)
    (hy : 0 ≤ y ∧ y > 0)
    (h1 : a^5 + b^5 ≤ 1)
    (h2 : x^5 + y^5 ≤ 1) :
    a^2 * x^3 + b^2 * y^3 ≤ 1 := by

  have h3 : a ^ 2 * x ^ 3 ≤ (2 / 5) * a ^ 5 + (3 / 5) * x ^ 5 := by
    have h31 : 0 < a := ha.right
    have h32 : 0 < x := hx.right
    apply lemma_1 a x h31 h32
  have h4 : b ^ 2 * y ^ 3 ≤ (2 / 5) * b ^ 5 + (3 / 5) * y ^ 5 := by
    have h41 : 0 < b := hb.right
    have h42 : 0 < y := hy.right
    apply lemma_1 b y h41 h42

  have h5 : a^2 * x^3 + b^2 * y^3 ≤ (2 / 5) * a ^ 5 + (3 / 5) * x ^ 5 + (2 / 5) * b ^ 5 + (3 / 5) * y ^ 5 := by
    linarith [h3, h4]
  have h6 : (2 / 5) * a ^ 5 + (3 / 5) * x ^ 5 + (2 / 5) * b ^ 5 + (3 / 5) * y ^ 5 ≤ 1 := by
    have h7 : a ^ 5 + b ^ 5 ≤ 1 := h1
    have h8 : x ^ 5 + y ^ 5 ≤ 1 := h2
    nlinarith
  linarith [h5, h6]