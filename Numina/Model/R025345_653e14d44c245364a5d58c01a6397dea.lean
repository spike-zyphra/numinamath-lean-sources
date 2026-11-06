import Mathlib


theorem inequalities_283794 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b + c + d = 4) :
    a^2 * b * c + b^2 * d * a + c^2 * d * a + d^2 * b * c ≤ 4 := by

  have h1 : a ^ 2 * b * c + b ^ 2 * d * a + c ^ 2 * d * a + d^2 * b * c = (a * b + c * d) * (a * c + b * d) := by
    ring
  rw [h1]

  have h2 : (a * b + c * d) * (a * c + b * d) ≤ 4 := by

    have h5 : (a * b + c * d) + (a * c + b * d) ≤ 4 := by
      have h3 : (a * b + c * d) + (a * c + b * d) = (a + d) * (b + c) := by
        nlinarith
      rw [h3]

      have h10 : (a + d) * (b + c) ≤ 4 := by
        have h11 : a + b + c + d = 4 := h
        nlinarith [sq_nonneg (a + d - (b + c)), sq_nonneg ((a + d + (b + c) : ℝ) - 4),
            mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd
        ]
      linarith

    nlinarith [sq_nonneg ((a * b + c * d) - (a * c + b * d)), sq_nonneg (a * b + c * d - 2), sq_nonneg (a * c + b * d - 2), mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd
      ]
  linarith