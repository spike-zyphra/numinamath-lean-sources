import Mathlib

theorem inequalities_122607 (a b c : ℝ) (ha : 0 < a) (hc : 0 < c) (hb : 0 < b)
    (hord : a ≥ b ∧ b ≥ c) (h : a * b * c = 1) (hsum : 1 / a + 1 / b + 1 / c < a + b + c) :
    a > 1 ∧ 1 > b := by
  have h1 : a ≥ b := hord.1
  have h2 : b ≥ c := hord.2

  have h3 : a * b + a * c + b * c < a + b + c := by
    have h4 : 0 < a * b * c := by
      positivity
    have h5 : (1 / a + 1 / b + 1 / c) * (a * b * c) = a * b + a * c + b * c := by
      field_simp
      <;> nlinarith
    have h6 : (a + b + c) * (a * b * c) = a + b + c := by
      rw [show a * b * c = 1 by linarith]
      all_goals nlinarith
    have h7 : (1 / a + 1 / b + 1 / c) * (a * b * c) < (a + b + c) * (a * b * c) := by
      apply mul_lt_mul_of_pos_right
      linarith [hsum]
      positivity
    nlinarith [h5, h6, h7]

  have ha1 : a > 1 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      h3, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

  have hb1 : 1 > b := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      h3, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

  constructor
  · linarith
  · linarith