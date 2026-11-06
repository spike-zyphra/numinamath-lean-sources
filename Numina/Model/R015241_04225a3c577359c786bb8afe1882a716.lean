import Mathlib

open Real

theorem inequalities_66093 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 = 1) :
    4 * sqrt 3 ≤ a + b + c + 1 / (a * b * c) := by
  have ha1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos 
    exact ha
    exact hb
    exact hc
  have h2 : a + b + c + 1 / (a * b * c) - 4 * sqrt 3 ≥ 0 := by
    have h3 : 0 < a * b * c := ha1
    have h4 : (sqrt 3) ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
    have h5 : (sqrt 3) ^ 4 = 9 := by
      calc 
        (sqrt 3) ^ 4 = ((sqrt 3) ^ 2) ^ 2 := by ring
        _ = (3) ^ 2 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
        _ = 9 := by norm_num
    have h6 : a + b + c + 1 / (a * b * c) - 4 * sqrt 3 ≥ 0 := by
      have h7 : a * b * c > 0 := by positivity
      have h8 : a + b + c + 1 / (a * b * c) - 4 * sqrt 3 = ( (a * b * c) * (a + b + c) + 1 - 4 * sqrt 3 * (a * b * c) ) / (a * b * c) := by
        field_simp
        <;> nlinarith
      rw [h8] at *
      apply div_nonneg
      have h10 : (a * b * c) * (a + b + c) + 1 - 4 * sqrt 3 * (a * b * c) ≥ 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (a^2 + b^2 + c^2 - 1), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, mul_pos (show 0 < a * b by nlinarith) (show 0 < a * c by nlinarith), mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith), mul_pos (show 0 < b * c by nlinarith) (show 0 < a * c by nlinarith), sq_nonneg (a + b + c - sqrt 3), sq_nonneg (a * b * c - Real.sqrt 3 / 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      linarith
      all_goals positivity
    linarith
  linarith