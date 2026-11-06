import Mathlib

theorem inequalities_245477 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 ≤ 1 / (1 + 2 * a) + 1 / (1 + 2 * b) + 1 / (1 + 2 * c) := by
  have h1 : 0 < (1 + 2 * a) * (1 + 2 * b) * (1 + 2 * c) := by
    positivity
  have h2 : 1 / (1 + 2 * a) + 1 / (1 + 2 * b) + 1 / (1 + 2 * c) - 1 ≥ 0 := by 
    have h3 : (1 + 2 * a) * (1 + 2 * b) * (1 + 2 * c) > 0 := by positivity
    have h4 : (1 / (1 + 2 * a) + 1 / (1 + 2 * b) + 1 / (1 + 2 * c) - 1) =
        ((1 + 2 * b) * (1 + 2 * c) + (1 + 2 * a) * (1 + 2 * c) + (1 + 2 * a) * (1 + 2 * b) - (1 + 2 * a) * (1 + 2 * b) * (1 + 2 * c)) / ((1 + 2 * a) * (1 + 2 * b) * (1 + 2 * c)) := by
      field_simp
      <;> ring
    rw [h4]
    apply div_nonneg 
    -- Here we need to prove that the numerator is non-negative
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_nonneg (a * b - 1), sq_nonneg (a * c - 1), sq_nonneg (b * c - 1),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, habc
      ]
    all_goals positivity
  linarith