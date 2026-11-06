import Mathlib

open Real

theorem inequalities_82449 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h1 : a ≤ 1) (h2 : b ≤ 1) :
    a / (b + 1) + b / (a + 1) ≤ 1 := by
  have h3 : 0 < b + 1 := by
    linarith
  have h4 : 0 < a + 1 := by
    linarith
  have h5 : a / (b + 1) + b / (a + 1) - 1 ≤ 0 := by
    have h6 : a / (b + 1) + b / (a + 1) - 1 =
        ( a * (a + 1) + b * (b + 1) - (b + 1) * (a + 1) ) / ((b + 1) * (a + 1)) := by
      field_simp
      <;> ring
    rw [h6] at *
    have h7 : a * (a + 1) + b * (b + 1) - (b + 1) * (a + 1) ≤ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - 1), sq_nonneg (b - 1), 
            mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2), 
            mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr (by linarith : 0 ≤ 1 - a)), 
            mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr (by linarith : 0 ≤ 1 - b)), 
            mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ b by linarith), 
            mul_nonneg (show (0 : ℝ) ≤ 1 - a by linarith) (show (0 : ℝ) ≤ 1 - b by linarith) ]
    have h8 : ( b + 1 ) * ( a + 1 ) > 0 := by
      positivity
    apply div_nonpos_of_nonpos_of_nonneg
    · linarith
    · positivity
  linarith
  all_goals linarith