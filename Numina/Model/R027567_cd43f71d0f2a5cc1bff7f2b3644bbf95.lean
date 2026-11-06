import Mathlib

open Real

theorem inequalities_4648
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (h : a + b + c = 2) :
    a ^ 2 / (b + c) + b ^ 2 / (c + a) + c ^ 2 / (a + b) ≥ 1 := by
  have h1 : 0 < b + c := by
    nlinarith
  have h2 : 0 < c + a := by
    nlinarith
  have h3 : 0 < a + b := by
    nlinarith
  have h4 : a ^ 2 / (b + c) + b ^ 2 / (c + a) + c ^ 2 / (a + b) - 1 ≥ 0 := by
    have h5 : a ^ 2 / (b + c) + b ^ 2 / (c + a) + c ^ 2 / (a + b) - 1 =
        (a ^ 2 * (c + a) * (a + b) + b ^ 2 * (b + c) * (a + b) + c ^ 2 * (b + c) * (c + a) - (b + c) * (c + a) * (a + b)) / ((b + c) * (c + a) * (a + b)) := by
      field_simp
      ring
    rw [h5]
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a + b + c - 2), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    all_goals
      positivity
  linarith