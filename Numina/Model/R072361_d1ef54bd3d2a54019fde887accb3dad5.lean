import Mathlib

theorem inequalities_131901 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a < b + c) : a / (1 + a) < b / (1 + b) + c / (1 + c) := by
  have h0 : 0 < a := ha
  have h1 : 0 < b := hb
  have h2 : 0 < c := hc
  have h3 : a < b + c := h
  have h4 : 0 < (1 + a) * (1 + b) * (1 + c) := by positivity

  have h5 : a * (1 + b) * (1 + c) - b * (1 + a) * (1 + c) - c * (1 + a) * (1 + b) < 0 := by
    nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_pos (sub_pos.mpr h) (show 0 < b by linarith), mul_pos (sub_pos.mpr h) (show 0 < c by linarith), mul_self_nonneg (a - b - c)]

  have h6 : a / (1 + a) - (b / (1 + b) + c / (1 + c)) < 0 := by
    have h7 : a / (1 + a) - (b / (1 + b) + c / (1 + c)) =
      (a * (1 + b) * (1 + c) - b * (1 + a) * (1 + c) - c * (1 + a) * (1 + b)) / ((1 + a) * (1 + b) * (1 + c)) := by
      field_simp
      ring
      all_goals nlinarith
    rw [h7]
    apply div_neg_of_neg_of_pos
    linarith
    positivity

  linarith