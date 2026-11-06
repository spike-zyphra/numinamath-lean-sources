import Mathlib

open Real

theorem inequalities_233378 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    216 ≤ ((1 + c) / a + 2) * ((1 + a) / b + 2) * ((1 + b) / c + 2) := by

  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc

  have h3 : ((1 + c) / a + 2) * ((1 + a) / b + 2) * ((1 + b) / c + 2) =
      ((1 + c + 2 * a) * (1 + a + 2 * b) * (1 + b + 2 * c)) / (a * b * c) := by
    field_simp
    <;> ring

  rw [h3] at *
  apply (le_div_iff₀ (by positivity)).mpr
  have h5 : ((1 + c + 2 * a) * (1 + a + 2 * b) * (1 + b + 2 * c)) ≥ 216 * (a * b * c) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a - 1 / 3), sq_nonneg (b - 1 / 3), sq_nonneg (c - 1 / 3),
        h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
      ]
  linarith