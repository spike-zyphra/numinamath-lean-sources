import Mathlib

theorem inequalities_601910 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    a ^ 2 / (2 + a) + b ^ 2 / (2 + b) + c ^ 2 / (2 + c) ≥ 1 := by
  have h1 : 0 < (2 + a) * (2 + b) * (2 + c) := by positivity
  have h2 : a ^ 2 / (2 + a) + b ^ 2 / (2 + b) + c ^ 2 / (2 + c) - 1 ≥ 0 := by
    have h3 : a ^ 2 / (2 + a) + b ^ 2 / (2 + b) + c ^ 2 / (2 + c) - 1 =
      (a ^ 2 * (2 + b) * (2 + c) + b ^ 2 * (2 + a) * (2 + c) + c ^ 2 * (2 + a) * (2 + b) - (2 + a) * (2 + b) * (2 + c)) / ((2 + a) * (2 + b) * (2 + c)) := by
      field_simp
      <;> ring
    rw [h3]
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_nonneg (a * b - 1), sq_nonneg (a * c - 1), sq_nonneg (b * c - 1),
      habc, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]
    all_goals positivity
  linarith