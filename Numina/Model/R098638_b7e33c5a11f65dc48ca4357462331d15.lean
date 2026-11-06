import Mathlib

theorem inequalities_152917 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 / 2 ≤ a / (b + c) + b / (c + a) + c / (a + b) := by
  have h1 : 0 < b + c := by linarith
  have h2 : 0 < c + a := by linarith
  have h3 : 0 < a + b := by linarith
  
  have h4 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 ≥ 0 := by
    have h5 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 =
        (1 / 2) * ( (a - b) ^ 2 / ((b + c) * (c + a)) + (b - c) ^ 2 / ((c + a) * (a + b)) + (c - a) ^ 2 / ((a + b) * (b + c)) ) := by
      field_simp
      ring
    rw [h5]
    have h6 : (a - b) ^ 2 / ((b + c) * (c + a)) ≥ 0 := by
      apply div_nonneg
      · apply pow_two_nonneg
      · nlinarith
    have h7 : (b - c) ^ 2 / ((c + a) * (a + b)) ≥ 0 := by
      apply div_nonneg
      · apply pow_two_nonneg
      · nlinarith
    have h8 : (c - a) ^ 2 / ((a + b) * (b + c)) ≥ 0 := by
      apply div_nonneg
      · apply pow_two_nonneg
      · nlinarith
    have h9 : (1 / 2) * ( (a - b) ^ 2 / ((b + c) * (c + a)) + (b - c) ^ 2 / ((c + a) * (a + b)) + (c - a) ^ 2 / ((a + b) * (b + c)) ) ≥ 0 := by
      nlinarith [h6, h7, h8]
    linarith
  linarith