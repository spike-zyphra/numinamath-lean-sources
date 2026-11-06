import Mathlib

theorem algebra_249327 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b * ((a + b) / 2 - c) + b * c * ((b + c) / 2 - a) +
      a * c * ((c + a) / 2 - b) = 0) : a = b ∧ b = c := by
  have h1 : (a - b) ^ 2 + (b - c) ^ 2 + (a - c) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
              sq_nonneg (a * (b - c)), sq_nonneg (b * (a - c)), sq_nonneg (c * (a - b)),
              mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
    ]
  have h2 : (a - b) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  have h3 : (b - c) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  have h4 : a - b = 0 := by
    nlinarith [pow_eq_zero h2]
  have h5 : b - c = 0 := by
    nlinarith [pow_eq_zero h3]
  have ha1 : a = b := by
    linarith
  have hb1 : b = c := by
    linarith
  exact ⟨ha1, hb1⟩