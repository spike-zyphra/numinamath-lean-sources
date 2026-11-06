import Mathlib

theorem inequalities_289482 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / (2 * a) + 1 / (2 * b) + 1 / (2 * c) ≥
    1 / (a + b) + 1 / (b + c) + 1 / (c + a) := by
  have pos1 : 0 < a := ha
  have pos2 : 0 < b := hb
  have pos3 : 0 < c := hc
  have pos4 : 0 < a * b := by positivity
  have pos5 : 0 < a * c := by positivity
  have pos6 : 0 < b * c := by positivity
  have pos7 : 0 < a * b * c := by positivity
  have pos8 : 0 < a + b := by positivity
  have pos9 : 0 < b + c := by positivity
  have pos10 : 0 < c + a := by positivity
  have h5 : 1 / (2 * a) + 1 / (2 * b) + 1 / (2 * c) - (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) ≥ 0 := by
    have h11 : 0 < a * b * c * (a + b) * (b + c) * (c + a) := by positivity
    have h12 : 1 / (2 * a) + 1 / (2 * b) + 1 / (2 * c) - (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) =
        ( (b * c * (a + b) * (b + c) * (c + a) +
            a * c * (a + b) * (b + c) * (c + a) +
            a * b * (a + b) * (b + c) * (c + a) ) - ( 2 * a * b * c * (b + c) * (c + a) +
            2 * a * b * c * (a + b) * (c + a) +
            2 * a * b * c * (a + b) * (b + c) ) ) / (2 * a * b * c * (a + b) * (b + c) * (c + a)) := by
      field_simp
      ring
    rw [h12]
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
      sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (a * (b - c)), 
      sq_nonneg (b * (a - b)), sq_nonneg (b * (a - c)), sq_nonneg (b * (b - c)), 
      sq_nonneg (c * (a - b)), sq_nonneg (c * (a - c)), sq_nonneg (c * (b - c)), 
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
      mul_pos hb ha, mul_pos hc ha, mul_pos hc hb, 
      mul_pos (show 0 < a * b by positivity) (show 0 < a * c by positivity), 
      mul_pos (show 0 < a * b by positivity) (show 0 < b * c by positivity), 
      mul_pos (show 0 < a * c by positivity) (show 0 < b * c by positivity)]
    positivity
  linarith