import Mathlib

theorem inequalities_314589 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    0 ≤ ((a - 1) * (c + 1) / (1 + b * c + c) + (b - 1) * (a + 1) / (1 + c * a + a) +
        (c - 1) * (b + 1) / (1 + a * b + b)) := by
  have h1 : 0 < (1 + b * c + c) * (1 + c * a + a) * (1 + a * b + b) := by
    positivity
  have h3 : (a - 1) * (c + 1) / (1 + b * c + c) + (b - 1) * (a + 1) / (1 + c * a + a) + (c - 1) * (b + 1) / (1 + a * b + b) =
          ((a - 1) * (c + 1) * (1 + c * a + a) * (1 + a * b + b) +
          (b - 1) * (a + 1) * (1 + b * c + c) * (1 + a * b + b) +
          (c - 1) * (b + 1) * (1 + b * c + c) * (1 + c * a + a)) / ((1 + b * c + c) * (1 + c * a + a) * (1 + a * b + b)) := by
    field_simp
    all_goals ring
  rw [h3] at *
  apply div_nonneg
  · -- Show the numerator is ≥ 0
    nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
      sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      sq_nonneg (a * b * c - 1), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
      mul_pos (mul_pos ha hb) hc
      ]
  · -- Show the denominator is ≥ 0
    positivity