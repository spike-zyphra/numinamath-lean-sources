import Mathlib

theorem inequalities_114494 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 / 2 ≤ a / (b + c) + b / (a + c) + c / (a + b) := by 
  have h1 : 0 < (b + c) * (a + c) * (a + b) := by
    positivity

  have h2 : a / (b + c) + b / (a + c) + c / (a + b) - 3 / 2 ≥ 0 := by
    have h3 : a / (b + c) + b / (a + c) + c / (a + b) - 3 / 2 =
      (2 * a * (a + c) * (a + b) + 2 * b * (b + c) * (a + b) + 2 * c * (b + c) * (a + c) - 3 * (b + c) * (a + c) * (a + b)) / (2 * (b + c) * (a + c) * (a + b)) := by
      field_simp
      ring
    rw [h3] at *
    apply div_nonneg
    · -- Show the numerator is ≥ 0
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (a * (b - c)),
        sq_nonneg (b * (a - b)), sq_nonneg (b * (a - c)), sq_nonneg (b * (b - c)),
        sq_nonneg (c * (a - b)), sq_nonneg (c * (a - c)), sq_nonneg (c * (b - c)),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
        ]
    · -- Show the denominator is > 0
      positivity

  linarith