import Mathlib

open Real

theorem inequalities_190217 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    9 / (2 * (a + b + c)) ≤ 1 / (b + c) + 1 / (a + c) + 1 / (a + b) := by

  have h1 : 0 < a := ha
  have h2 : 0 < b := hb
  have h3 : 0 < c := hc

  have h4 : 0 < b + c := by linarith
  have h5 : 0 < a + c := by linarith
  have h6 : 0 < a + b := by linarith
  have h7 : 0 < a + b + c := by linarith
  
  have h9 : 1 / (b + c) + 1 / (a + c) + 1 / (a + b) - 9 / (2 * (a + b + c)) ≥ 0 := by
    have h10 : 0 < (b + c) := by linarith
    have h11 : 0 < (a + c) := by linarith
    have h12 : 0 < (a + b) := by linarith
    have h13 : 0 < (a + b + c) := by linarith
    have h14 : 0 < (b + c) * (a + c) * (a + b) := by positivity
    have h15 : 0 < 2 * (a + b + c) := by nlinarith
    have h18 : (1 / (b + c) + 1 / (a + c) + 1 / (a + b) - 9 / (2 * (a + b + c))) =
        ( (2 * (a + b + c) * ((a + c) * (a + b)) + 2 * (a + b + c) * ((b + c) * (a + b)) + 2 * (a + b + c) * ((b + c) * (a + c)) - 9 * ((b + c) * (a + c) * (a + b)) ) / ((b + c) * (a + c) * (a + b) * (2 * (a + b + c)))
      ) := by 
      field_simp
      ring
    rw [h18] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]
    all_goals positivity
  
  linarith