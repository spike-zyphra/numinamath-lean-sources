import Mathlib

theorem inequalities_52360 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    a + b + c ≥ Real.sqrt ((1 / 3) * (a + 2) * (b + 2) * (c + 2)) := by
  have h2 : (a + b + c) ^ 2 ≥ (1 / 3) * (a + 2) * (b + 2) * (c + 2) := by
    nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
              sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
              sq_nonneg (a * b * c - 1),
              mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, habc]

  have h3 : a + b + c ≥ 0 := by nlinarith

  have h5 : Real.sqrt ((1 / 3) * (a + 2) * (b + 2) * (c + 2)) ≤ a + b + c := by
    have h6 : Real.sqrt ((1 / 3) * (a + 2) * (b + 2) * (c + 2)) ≤ Real.sqrt ((a + b + c) ^ 2) := by
      apply Real.sqrt_le_sqrt
      linarith [h2]
    have h7 : Real.sqrt ((a + b + c) ^ 2) = a + b + c := by
      rw [Real.sqrt_sq]
      linarith
    linarith [h6, h7]

  linarith [h5]