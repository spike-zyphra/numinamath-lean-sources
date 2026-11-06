import Mathlib

theorem inequalities_80218 (a b c : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) (hc : 0 ≤ c ∧ c ≤ 1) :
    a / (b * c + 1) + b / (a * c + 1) + c / (a * b + 1) ≤ 2 := by 
  have ha1 : 0 ≤ a := ha.1
  have ha2 : a ≤ 1 := ha.2
  have hb1 : 0 ≤ b := hb.1
  have hb2 : b ≤ 1 := hb.2
  have hc1 : 0 ≤ c := hc.1
  have hc2 : c ≤ 1 := hc.2
  have h1 : 0 ≤ a * b := by nlinarith
  have h2 : 0 ≤ a * c := by nlinarith
  have h3 : 0 ≤ b * c := by nlinarith
  have h4 : 0 ≤ a * b * c := by nlinarith
  have pos1 : b * c + 1 > 0 := by nlinarith
  have pos2 : a * c + 1 > 0 := by nlinarith
  have pos3 : a * b + 1 > 0 := by nlinarith
  have h5 : a / (b * c + 1) + b / (a * c + 1) + c / (a * b + 1) - 2 ≤ 0 := by
    have h6 : a / (b * c + 1) + b / (a * c + 1) + c / (a * b + 1) - 2 =
        (a * (a * c + 1) * (a * b + 1) + b * (b * c + 1) * (a * b + 1) + c * (b * c + 1) * (a * c + 1) - 2 * (b * c + 1) * (a * c + 1) * (a * b + 1)) / ((b * c + 1) * (a * c + 1) * (a * b + 1)) := by
      field_simp [pos1, pos2, pos3]
      ring
    rw [h6]
    have h7 : a * (a * c + 1) * (a * b + 1) + b * (b * c + 1) * (a * b + 1) + c * (b * c + 1) * (a * c + 1) - 2 * (b * c + 1) * (a * c + 1) * (a * b + 1) ≤ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (b - c)), sq_nonneg (b * (a - c)), sq_nonneg (c * (a - b)),
        mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ 1 - a by linarith),
        mul_nonneg (show (0 : ℝ) ≤ b by linarith) (show (0 : ℝ) ≤ 1 - b by linarith),
        mul_nonneg (show (0 : ℝ) ≤ c by linarith) (show (0 : ℝ) ≤ 1 - c by linarith)
       ]
    apply div_nonpos_of_nonpos_of_nonneg h7 (by positivity)
  linarith