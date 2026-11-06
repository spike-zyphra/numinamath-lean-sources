import Mathlib

theorem inequalities_7808 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h1 : a ≤ 1) (h2 : b ≤ 1) (h3 : c ≤ 1) :
    a / (1 + b * c) + b / (1 + a * c) + c / (1 + a * b) ≤ 2 := by
  have h4 : 0 ≤ a * b * c := by
    apply mul_nonneg
    apply mul_nonneg
    all_goals linarith
  have h5 : 0 < 1 + b * c := by nlinarith
  have h6 : 0 < 1 + a * c := by nlinarith
  have h7 : 0 < 1 + a * b := by nlinarith
  have h8 : a / (1 + b * c) + b / (1 + a * c) + c / (1 + a * b) - 2 ≤ 0 := by
    have h9 : a / (1 + b * c) + b / (1 + a * c) + c / (1 + a * b) - 2 =
        (a * (1 + a * c) * (1 + a * b) + b * (1 + b * c) * (1 + a * b) + c * (1 + b * c) * (1 + a * c) - 2 * (1 + b * c) * (1 + a * c) * (1 + a * b)) / ((1 + b * c) * (1 + a * c) * (1 + a * b)) := by
      field_simp
      ring
    rw [h9]
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show the numerator is ≤ 0
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2), 
          mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h3), 
          mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr h3), 
          mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ 1 - a by linarith), 
          mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ 1 - b by linarith), 
          mul_nonneg (show 0 ≤ c by linarith) (show 0 ≤ 1 - c by linarith)
        ]
    · -- Show the denominator is ≥ 0
      positivity
  linarith