import Mathlib

open Real

theorem inequalities_602628 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 / 2 ≤ a / (b + c) + b / (c + a) + c / (a + b) := by
  have ha1 : 0 < b := hb
  have ha2 : 0 < c := hc
  have ha3 : 0 < a := ha
  have pos1 : 0 < b + c := by linarith
  have pos2 : 0 < c + a := by linarith
  have pos3 : 0 < a + b := by linarith
  have h1 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 ≥ 0 := by
    have pos4 : 0 < b + c := by linarith
    have pos5 : 0 < c + a := by linarith
    have pos6 : 0 < a + b := by linarith
    have h2 : (a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2) =
        (2 * (a * (c + a) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (c + a))
          - 3 * (b + c) * (c + a) * (a + b)) / (2 * (b + c) * (c + a) * (a + b)) := by
      field_simp
      ring
    rw [h2]
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
        sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), 
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
      ]
    positivity
  linarith