import Mathlib

theorem inequalities_41192 (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b : ℝ) / (a + c) + (b + c) / (b + a) + (c + a) / (c + b) ≤
    (a / b : ℝ) + (b / c : ℝ) + (c / a : ℝ) := by
  have ha1 : 0 < (a : ℝ) := by exact_mod_cast ha
  have hb1 : 0 < (b : ℝ) := by exact_mod_cast hb
  have hc1 : 0 < (c : ℝ) := by exact_mod_cast hc
  have pos1 : (a : ℝ) + c > 0 := by positivity
  have pos2 : (b : ℝ) + a > 0 := by positivity
  have pos3 : (c : ℝ) + b > 0 := by positivity
  have h4 : (a + b : ℝ) / (a + c) + (b + c) / (b + a) + (c + a) / (c + b) - (a / b : ℝ) - (b / c : ℝ) - (c / a : ℝ) ≤ 0 := by
    have pos1' : (a + c) ≠ 0 := by positivity
    have pos2' : (b + a) ≠ 0 := by positivity
    have pos3' : (c + b) ≠ 0 := by positivity
    have pos4' : (b : ℝ) ≠ 0 := by positivity
    have pos5' : (c : ℝ) ≠ 0 := by positivity
    have pos6' : (a : ℝ) ≠ 0 := by positivity
    have h5 : (a + b : ℝ) / (a + c) + (b + c) / (b + a) + (c + a) / (c + b) - (a / b : ℝ) - (b / c : ℝ) - (c / a : ℝ) =
        ((a + b) * b * c * a * (b + a) * (c + b) +
        (b + c) * b * c * a * (a + c) * (c + b) +
        (c + a) * b * c * a * (a + c) * (b + a) -
        a * c * a * (a + c) * (b + a) * (c + b) -
        b * b * a * (a + c) * (b + a) * (c + b) -
        c * b * c * (a + c) * (b + a) * (c + b)) / 
        ((a * b * c * (a + c) * (b + a) * (c + b) : ℝ)) := by
      field_simp [pos1', pos2', pos3', pos4', pos5', pos6']
      ring
    rw [h5]
    apply div_nonpos_of_nonpos_of_nonneg
    nlinarith [sq_nonneg ((a : ℝ) - (b : ℝ)), sq_nonneg ((b : ℝ) - (c : ℝ)), sq_nonneg ((c : ℝ) - (a : ℝ)),
        sq_nonneg ((a : ℝ) * (b - c)), sq_nonneg ((b : ℝ) * (c - a)), sq_nonneg ((c : ℝ) * (a - b)),
        mul_pos ha1 hb1, mul_pos hb1 hc1, mul_pos ha1 hc1,
        mul_pos ha1 pos1, mul_pos ha1 pos2, mul_pos ha1 pos3,
        mul_pos hb1 pos1, mul_pos hb1 pos2, mul_pos hb1 pos3,
        mul_pos hc1 pos1, mul_pos hc1 pos2, mul_pos hc1 pos3
        ]
    positivity
  linarith