import Mathlib

theorem inequalities_46389 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    3 / 2 ≤ a / (1 + b) + b / (1 + c) + c / (1 + a) := by
  have h1 : 0 < a := ha
  have h2 : 0 < b := hb
  have h3 : 0 < c := hc

  have h4 : 0 < (1 + b) * (1 + c) * (1 + a) := by positivity
  have h5 : a / (1 + b) + b / (1 + c) + c / (1 + a) - 3 / 2 ≥ 0 := by
    have pos1 : 0 < (1 + b) := by linarith
    have pos2 : 0 < (1 + c) := by linarith
    have pos3 : 0 < (1 + a) := by linarith
    have h6 : a / (1 + b) + b / (1 + c) + c / (1 + a) - 3 / 2 =
        (a * (1 + c) * (1 + a) + b * (1 + b) * (1 + a) + c * (1 + b) * (1 + c) - 3 / 2 * ( (1 + b) * (1 + c) * (1 + a) )) / ((1 + b) * (1 + c) * (1 + a)) := by 
      field_simp 
      <;> ring
      <;> field_simp
      <;> ring
      <;> nlinarith
    rw [h6]
    apply div_nonneg 
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
      sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
      mul_pos (show 0 < a * b by nlinarith) (show 0 < c by linarith), 
      mul_pos (show 0 < b * c by nlinarith) (show 0 < a by linarith), 
      habc
      ]
    all_goals positivity
  linarith