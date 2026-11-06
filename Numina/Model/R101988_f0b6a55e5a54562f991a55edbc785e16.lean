import Mathlib.Tactic

theorem inequalities_139384
    (a b c d : ℝ)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hc : 0 ≤ c)
    (hd : 0 ≤ d)
    (h5 : a^5 + b^5 ≤ 1)
    (h6 : c^5 + d^5 ≤ 1) :
    a^2 * c^3 + b^2 * d^3 ≤ 1 := by 
  have h1 : a^2 * c^3 ≤ (2 / 5) * a^5 + (3 / 5) * c^5 := by
    nlinarith [sq_nonneg (a ^ 2 - c ^ 2), sq_nonneg (a * c - c ^ 2), sq_nonneg (a ^ 3 - c * a ^ 2), sq_nonneg (a - c),
          mul_nonneg ha hc, mul_nonneg ha hd, mul_nonneg hb hc, mul_nonneg hb hd,
          pow_two_nonneg (a - 1), pow_two_nonneg (c - 1),
          pow_two_nonneg (a ^ 2 - c ^ 2), pow_two_nonneg (a ^ 3 - c ^ 3)]
  have h2 : b^2 * d^3 ≤ (2 / 5) * b^5 + (3 / 5) * d^5 := by
    nlinarith [sq_nonneg (b ^ 2 - d ^ 2), sq_nonneg (b * d - d ^ 2), sq_nonneg (b ^ 3 - d * b ^ 2), sq_nonneg (b - d),
            mul_nonneg hb hc, mul_nonneg hb hd, mul_nonneg ha hc, mul_nonneg ha hd,
            pow_two_nonneg (b - 1), pow_two_nonneg (d - 1),
            pow_two_nonneg (b ^ 2 - d ^ 2), pow_two_nonneg (b ^ 3 - d ^ 3)]
  linarith [h1, h2, h5, h6]