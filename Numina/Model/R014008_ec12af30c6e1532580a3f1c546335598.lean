import Mathlib


theorem inequalities_603444 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hord : b ≥ a ∧ c ≥ b) (hsum : a + b + c = 1 / a + 1 / b + 1 / c) :
    a * b^2 * c^3 ≥ 1 := by

  have h1 : 0 < a * b * c := by
    positivity

  have h2 : (a + b + c) * (a * b * c) = (b * c + a * c + a * b) := by
    have eq2 : a + b + c = 1 / a + 1 / b + 1 / c := by linarith
    have eq3 : (a + b + c) * (a * b * c) = (1 / a + 1 / b + 1 / c) * (a * b * c) := by
      rw [eq2]
    have eq4 : (1 / a + 1 / b + 1 / c) * (a * b * c) = (b * c + a * c + a * b) := by
      field_simp
      <;> ring
    linarith [eq3, eq4]

  have h3 : b ≥ a := hord.1
  have h4 : c ≥ b := hord.2
  have h5 : c ≥ a := by linarith

  have h6 : a * b^2 * c^3 ≥ 1 := by
    nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (a * c - 1),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c),
      mul_nonneg (show 0 ≤ (b - a) by linarith) (show 0 ≤ (c - b) by linarith),
      mul_nonneg (show 0 ≤ (c - b) by linarith) (show 0 ≤ (c - a) by nlinarith),
      mul_nonneg (show 0 ≤ (c - a) by nlinarith) (show 0 ≤ (b - a) by linarith),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
      mul_nonneg (show 0 ≤ (b - a) by linarith) (show 0 ≤ (c) by linarith),
      mul_nonneg (show 0 ≤ (c - b) by linarith) (show 0 ≤ (c) by linarith),
      mul_nonneg (show 0 ≤ (c) by linarith) (show 0 ≤ (c - b) by linarith),
      mul_nonneg (show 0 ≤ (b) by linarith) (show 0 ≤ (c - b) by linarith),
      mul_nonneg (show 0 ≤ (c - a) by nlinarith) (show 0 ≤ (c) by linarith)
    ]
  exact h6