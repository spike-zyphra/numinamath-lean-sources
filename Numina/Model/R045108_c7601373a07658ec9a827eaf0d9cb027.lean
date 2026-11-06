import Mathlib

theorem inequalities_87649 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 2) :
    27 / 13 ≤ 1 / (1 + a * b) + 1 / (1 + b * c) + 1 / (1 + c * a) := by
  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : 0 < b * c := mul_pos hb hc
  have h3 : 0 < c * a := mul_pos hc ha

  have h4 : 1 / (1 + a * b) + 1 / (1 + b * c) + 1 / (1 + c * a) - 27 / 13 ≥ 0 := by
    have h5 : 0 < (1 + a * b) * (1 + b * c) * (1 + c * a) := by
      positivity
    have h6 : 1 / (1 + a * b) + 1 / (1 + b * c) + 1 / (1 + c * a) - 27 / 13 =
        (13 * ( (1 + b * c) * (1 + c * a) + (1 + a * b) * (1 + c * a) + (1 + a * b) * (1 + b * c) ) - 27 * (1 + a * b) * (1 + b * c) * (1 + c * a) ) / (13 * (1 + a * b) * (1 + b * c) * (1 + c * a)) := by
      field_simp
      ring
    rw [h6]

    have h7 : 13 * ( (1 + b * c) * (1 + c * a) + (1 + a * b) * (1 + c * a) + (1 + a * b) * (1 + b * c) ) - 27 * (1 + a * b) * (1 + b * c) * (1 + c * a) ≥ 0 := by
      have h8 : c = 2 - a - b := by linarith
      rw [h8]
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - (2 - a - b)), sq_nonneg (a - (2 - a - b)), sq_nonneg (a * b - b * (2 - a - b)), sq_nonneg (b * (2 - a - b) - (2 - a - b) * a), sq_nonneg ((2 - a - b) * a - a * b), mul_pos ha hb, mul_pos hb (show 0 < 2 - a - b by nlinarith), mul_pos (show 0 < 2 - a - b by nlinarith) ha, sq_nonneg (a + b - (2 - a - b)), sq_nonneg (a * b + b * (2 - a - b) + (2 - a - b) * a - 4 / 3)]

    have h8 : (13 * ( (1 + b * c) * (1 + c * a) + (1 + a * b) * (1 + c * a) + (1 + a * b) * (1 + b * c) ) - 27 * (1 + a * b) * (1 + b * c) * (1 + c * a) ) / (13 * (1 + a * b) * (1 + b * c) * (1 + c * a)) ≥ 0 := by
      apply div_nonneg
      linarith
      positivity
    linarith

  linarith