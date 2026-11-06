import Mathlib

theorem algebra_178135 {a b : ℝ} (ha : a > 0) (hb : b > 0)
    (h1 : 120 / a = 120 / b + 6) (h2 : 120 / (a * (1 + 1 / 4)) = 120 / (b * (1 + 1 / 5)) + 4) :
    a = 4 ∧ b = 5 := by
  have eq3 : 6 * a * b + 120 * a - 120 * b = 0 := by
    field_simp at h1
    nlinarith
  have eq4 : 4 * a * b + 100 * a - 96 * b = 0 := by
    field_simp at h2
    nlinarith
  have h3 : a = 4 := by
    nlinarith [sq_nonneg (a - 4), sq_nonneg (b - 5), sq_nonneg (a - b), mul_pos ha hb]
  have h4 : b = 5 := by
    nlinarith [sq_nonneg (a - 4), sq_nonneg (b - 5), sq_nonneg (a - b), mul_pos ha hb
      ]
  constructor
  · exact h3
  · exact h4